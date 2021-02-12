/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.debug;

import java.net.URI;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.stream.Collectors;

import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.ScopePresentationHint;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.Value;
import util.Assert;
import util.Assert.TLCDetailedRuntimeException;
import util.Assert.TLCRuntimeException;
import util.UniqueString;

public class TLCStackFrame extends StackFrame {
	
	// Not thread-safe because TLCDebugger is assumed to take care of synchronization!
	private static final Map<SemanticNode, String> PATH_CACHE = new HashMap<>();

	public static final String EXCEPTION = "Exception";
	public static final String CONSTANTS = "Constants";
	public static final String SCOPE = "Context";
	public static final String STACK = "Stack";
	
	// It would be easier to use hashCode instead of passing a random generator
	// around. However, calculating the hashCode for a TLC value calculates the
	// value's fingerprint, which normalizes and, thus, enumerates the value.
	protected static final Random rnd = new Random();

	protected transient final Map<Integer, DebugTLCVariable> nestedVariables = new HashMap<>();
	protected transient final Map<Integer, List<DebugTLCVariable>> nestedConstants = new HashMap<>();

	protected transient final SemanticNode node;
	protected transient final Context ctxt;
	protected transient final Tool tool;
	protected transient final RuntimeException exception;
	// null if this is the root frame, i.e. the start of an evaluation.
	protected transient TLCStackFrame parent;

	protected final int ctxtId;
	
	// Testing only!
	TLCStackFrame(int id) {
		super();
		this.node = null;
		this.ctxt = null;
		this.tool = null;
		this.exception = null;
		this.ctxtId = -1;
		this.setId(id);
	}

	public TLCStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, Tool tool, RuntimeException e) {
		this.parent = parent;
		this.tool = tool;
		Assert.check(this.tool != null, EC.GENERAL);
		
		if (e instanceof TLCDetailedRuntimeException) {
			TLCDetailedRuntimeException dre = (TLCDetailedRuntimeException) e;
			this.node = dre.expr;
			this.ctxt = dre.ctxt;
		} else {
			this.node = node;
			// Do not create a deep copy of ctxt (like it is done for state and predecessor
			// in TLCInit|NextStackFrame. A TLCStackFrame will point to its corresponding
			// node in the Context tree even if Context mutates.
			this.ctxt = ctxt; //ctxt.deepCopy();
		}
		Assert.check(this.node != null, EC.GENERAL);
		Assert.check(this.ctxt != null, EC.GENERAL);

		this.exception = e; // e is nullable!

		if (node instanceof NumeralNode) {
			setName(Integer.toString(((NumeralNode)node).val()));
		} else {
			setName(node.getHumanReadableImage());
		}
		// There is a 1:n mapping between SemanticNode and TLCStackFrames. For example,
		// the same SN appears multiple times on the stack in case of recursion. Thus,
		// node.myUID doesn't suffice as a frame's id, which - by definition - has to
		// be unique across all frames.
		setId(node.myUID ^ rnd.nextInt(Integer.MAX_VALUE - 1) + 1);

		final Location location = node.getLocation();
		setLine(location.beginLine());
		setEndLine(location.endLine());
		setColumn(location.beginColumn());
		setEndColumn(location.endColumn()+1);

		final Source source = new Source();
		source.setName(node.getLocation().source());
		// resolve(..) triggers a file-system round-trip (IO), which is obviously too
		// expensive!!! Thus, cache the result.
		source.setPath(PATH_CACHE.computeIfAbsent(node,
				n -> tool.getResolver().resolve(n.getTreeNode().getFilename(), true).getAbsolutePath().toString()));
		setSource(source);
		
		this.ctxtId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
	}

	public TLCStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, final Tool tool) {
		this(parent, node, ctxt, tool, null);
	}

	protected Variable getVariable(final IValue value, String varName) {
		return getVariable(value, UniqueString.of(varName));
	}
	
	protected Variable getVariable(final IValue value, UniqueString varName) {
		DebugTLCVariable variable = (DebugTLCVariable) value.toTLCVariable(new DebugTLCVariable(varName), rnd);
		nestedVariables.put(variable.getVariablesReference(), variable);
		return variable;
	}

	Variable[] getVariables() {
		return getVariables(ctxtId);
	}

	Variable[] getConstants() {
		return getVariables(ctxtId + 1);
	}
	
	Variable[] getException() {
		return getVariables(ctxtId + 2);
	}
	
	public Variable[] getVariables(final int vr) {
		return tool.eval(() -> {
			final List<Variable> vars = new ArrayList<>();

			if (nestedVariables.containsKey(vr)) {
				List<TLCVariable> nested = nestedVariables.get(vr).getNested(rnd);
				for (TLCVariable n : nested) {
					DebugTLCVariable d = (DebugTLCVariable) n;
					nestedVariables.put(d.getVariablesReference(), d);
					vars.add(d);
				}
			}

			if (nestedConstants.containsKey(vr)) {
				List<DebugTLCVariable> cntsts = nestedConstants.get(vr);
				for (DebugTLCVariable c : cntsts) {
					nestedVariables.put(c.getVariablesReference(), c);
					List<TLCVariable> nested = c.getNested(rnd);
					for (TLCVariable n : nested) {
						DebugTLCVariable d = (DebugTLCVariable) n;
						nestedVariables.put(d.getVariablesReference(), d);
					}
				}
				vars.addAll(cntsts);
			}
			
			if (vr == ctxtId + 2) {
				final Variable variable = new Variable();
				variable.setName(getNode().getHumanReadableImage());
				final RuntimeException re = (RuntimeException) exception;
				variable.setValue(re.getMessage());
				variable.setType(re.getClass().getSimpleName()); //TODO Is this useful?
				vars.add(variable);
			}

			if (ctxtId == vr) {
				Context c = this.ctxt;
				while (c.hasNext()) {
					Object val = c.getValue();
					if (val instanceof LazyValue) {
						// unlazy/eval LazyValues
						val = unlazy((LazyValue) c.getValue());
					}
					if (val instanceof Value) {
						vars.add(getVariable((Value) val, c.getName().getName().toString()));
					} else if (val instanceof SemanticNode) {
						final Variable variable = new Variable();
						variable.setName(c.getName().getSignature());
						variable.setValue(((SemanticNode) val).getHumanReadableImage());
						vars.add(variable);
					} else if (val instanceof RuntimeException) {
						final Variable variable = new Variable();
						variable.setName(c.getName().getName().toString());
						variable.setValue(c.getValue().toString());
						final RuntimeException re = (RuntimeException) val;
						variable.setType(re.getMessage());
						vars.add(variable);
					} else {
						System.err.println("This is interesting!!! What's this??? " + val.toString());
					}
					c = c.next();
				}
			} else if (ctxtId + 1 == vr) {
				//TODO: This is evaluated for each TLCStackFrame instance even though the constantDefns
				// never change.  Perhaps, this can be moved to a place where it's only evaluated once.
				// On the other hand, the debug adapter protocol (DAP) might not like sharing
				// DebugTLCVariables.
				final SpecProcessor sp = this.tool.getSpecProcessor();
				final Map<ModuleNode, Map<OpDefNode, Object>> constantDefns = sp.getConstantDefns();
				for (final Entry<ModuleNode, Map<OpDefNode, Object>> e : constantDefns.entrySet()) {
					final ModuleNode module = e.getKey();
					
					final Variable v = new Variable();
					// Pick one of the OpDefNode and derive the name with which the definition
					// appears in the spec, i.e. A!B!C!Op -> A!B!C.  Users then see the module
					// name and instance path that appears in the instantiating module. getPathName
					// equals the empty (unique) string if the module has no path.
					v.setValue(e.getValue().keySet().stream().findAny().map(odn -> odn.getPathName())
							.orElse(UniqueString.of(module.getSignature())).toString());
					v.setName(module.getSignature());
					v.setVariablesReference(rnd.nextInt(Integer.MAX_VALUE - 1) + 1);

					nestedConstants.put(v.getVariablesReference(),
							e.getValue().entrySet().stream().filter(f -> f.getValue() instanceof Value)
									.map(f -> (DebugTLCVariable) ((Value) f.getValue())
											.toTLCVariable(new DebugTLCVariable(f.getKey().getLocalName()), rnd))
									.collect(Collectors.toList()));
					vars.add(v);
				}
			}
			return toSortedArray(vars);
		});
	}
	
	protected Variable[] toSortedArray(final List<Variable> vars) {
		// Its nicer if the variables/constants are sorted lexicographically.
		vars.sort(new Comparator<Variable>() {
			@Override
			public int compare(Variable o1, Variable o2) {
				return o1.getName().compareTo(o2.getName());
			}
		});
		return vars.toArray(new Variable[vars.size()]);
	}
	
	protected Variable getVariable(final LinkedList<SemanticNode> path) {
		assert !path.isEmpty();
		
		SemanticNode sn = path.getFirst();
		SymbolNode node = null;
		if (sn instanceof OpArgNode) {
			node = ((OpArgNode) sn).getOp();
		} else if (sn instanceof OpApplNode) {
			node = ((OpApplNode) sn).getOperator();
		} else if (sn instanceof SymbolNode) {
			node = (SymbolNode) sn;
		}

		Object o;
		if (node != null) {
			// lookup might return sn, in which case hover will show the nodes location.
			o = tool.lookup(node, this.ctxt, false);
		} else {
			o = sn;
		}

		final Variable variable = new Variable();
		if (o instanceof SymbolNode && ((SymbolNode)o).isBuiltIn()) {
			variable.setValue(((SymbolNode)o).getLocation().toString());
		} else {
			variable.setValue(o.toString());
		}
		variable.setType(o.getClass().getSimpleName());
		return variable;
	}

	public EvaluateResponse get(final EvaluateArguments ea) {
		// Lets assume a module R that extends B, which in turn instantiates module A,
		// i.e., R e> B i> A where "e>" denotes extends and "i>" denotes
		// instantiation.
		// For two constants c defined in A and B, and foo defined in R, the DAP variable
		// view shows a high-level "Constants" and a sub-node for A, B, and R, respectively:
		//
		// Constant
		// - A
		// -- c
		// - B
		// -- c
		// - R
		// -- foo
		// -- ...
		//
		// A user might hover of the occurrence of constant c in R, which should be evaluated
		// to the value of B!c.  She might also hover over the occurrence of I!c in R, assuming
		// an named instantiation, i.e. I == INSTANCE A occurring in B.  If she opens module A,
		// hovering over c should also show the value of A!c.  Hovering of c in B, on the other
		// hand, has to show the value of B!c.
		//
		// Unless TLCDebugger declares the capability "EvaluateForHovers" [0], DAP uses a
		// basic lookup mechanism that looks for symbols in the set of variables from which DAP
		// populated its variables view.  This mechanism fails to resolve a symbol if it appears
		// multiple times such as c above.  It also fails to handle the case of variables appearing
		// in sub-nodes such as R.  That is, it doesn't not resolve foo because foo is one level
		// too deep in the tree.  In other words, the lookup mechanism is coupled to how the view
		// presents the data.  To address these issues, TLCDebugger declares the capability
		// "EvaluateForHovers" and resolves variables manually.
		// DAP does not provide the current (hovering) location (file, start/end line & column) as
		// structured data [1].  Instead, we encode the location into the expression of
		// EvaluateArguments as suggested privately by Andre Weinand of the VSCode team and
		// partially demonstrated by vscode-mock-debug [2].
		// 
		//
		// [0] https://microsoft.github.io/debug-adapter-protocol/specification#Requests_Evaluate
		// [1] https://github.com/microsoft/vscode/issues/89084
		// [2] https://github.com/microsoft/vscode-mock-debug/commit/27539c78c25aa316be6aa1ee03bfd1e87bf7faad#diff-04bba6a35cad1c794cbbe677678a51de13441b7a6ee8592b7b50be1f05c6f626

		// Encode this file, token, and range into a URI with which parsing becomes a
		// no-brainer but some might consider over-engineered, oh well...
		// tlaplus:///home/markus/foo/bar.tla?A!c#4 3 1 2
		final EvaluateResponse er = new EvaluateResponse();
		try {
			final URI u = URI.create(ea.getExpression());
			// Unfortunately, we have to manually strip the extension because the lookup
			// later is going to be on the module, not the file name.
			final String moduleName = Paths.get(u.getPath()).getFileName().toString().replaceAll(".tla$", "");

			final Location location = Location.parseCoordinates(moduleName, u.getFragment());
			final LinkedList<SemanticNode> path = tool.getModule(location.source()).pathTo(location);
			if (path.isEmpty()) {
				// Can be resolved to something. If not, the user hovered over something like a comment.
				er.setResult(location.toString());
				return er;
			}
			final Variable v = getVariable(path);
			if (v != null) {
				// Can be resolved to something. If not, the user hovered over something like a comment.
				er.setResult(v.getValue());
				er.setType(v.getType());
				er.setVariablesReference(v.getVariablesReference());
			}
			
			return er;
		} catch (IllegalArgumentException e) {
			return er;
		}
	}

	protected Object unlazy(final LazyValue lv) {
		try {
			return tool.eval(() -> {
				return lv.eval(tool);
			});
		} catch (TLCRuntimeException | EvalException e) {
			return e;
		}
	}

	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		
		if (!ctxt.isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(SCOPE);
			scope.setVariablesReference(ctxtId);
			scopes.add(scope);
		}
		
		if (!this.tool.getSpecProcessor().getConstantDefns().isEmpty()) {
			final Scope scope = new Scope();
			scope.setName(CONSTANTS);
			scope.setVariablesReference(ctxtId + 1);
			scope.setPresentationHint(ScopePresentationHint.REGISTERS);
			scopes.add(scope);
		}

		if (this.exception != null) {
			final Scope scope = new Scope();
			scope.setName(EXCEPTION);
			scope.setVariablesReference(ctxtId + 2);
			scopes.add(scope);
		}
		
		return scopes.toArray(new Scope[scopes.size()]);
	}
	
	public SemanticNode getNode() {
		return node;
	}

	public Context getContext() {
		return ctxt;
	}

	public Tool getTool() {
		return tool;
	}

	@Override
	public String toString() {
		return "TLCStackFrame [node=" + node + "]";
	}

	public Value setValue(Value v) {
		return v;
	}
}