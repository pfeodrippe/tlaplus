# Claude Code Agent Skills - Properly Structured

This project now includes properly formatted Agent Skills following the Claude Code official structure.

## Skill Directory Structure

```
.claude/skills/
├── tlc-test-execution/
│   └── SKILL.md
├── tla-model-creation/
│   └── SKILL.md
├── tlc-global-state-management/
│   └── SKILL.md
├── tlc-multi-run-test-design/
│   └── SKILL.md
└── tlc-debugging-state-issues/
    └── SKILL.md
```

## Skills Available

### 1. tlc-test-execution
**When to use**: Executing TLC model-checking tests and interpreting results

**File**: `.claude/skills/tlc-test-execution/SKILL.md`

**Capabilities**:
- Execute TLC tests via Ant
- Interpret test output
- Check TLC exit codes (0, 2110, 2230)
- Verify test status

**Example**:
```bash
ant -f customBuild.xml test-set -Dtest.testcases="tlc2/tool/RunTwicePersistentFlagTest.java"
```

---

### 2. tla-model-creation
**When to use**: Creating and configuring TLA+ model specifications

**File**: `.claude/skills/tla-model-creation/SKILL.md`

**Capabilities**:
- Create `.tla` specification files
- Create `.cfg` configuration files
- Design state machines and invariants
- Write templates and best practices

**Key Requirement**: Each model must be DIFFERENT (unique variables, different logic)

---

### 3. tlc-global-state-management
**When to use**: Managing TLCGlobals and persistent state across multiple runs

**File**: `.claude/skills/tlc-global-state-management/SKILL.md`

**Capabilities**:
- Reset TLCGlobals and related state
- Verify state changes
- Check object identity
- Manage complete reset sequence

**Reset Sequence**:
```java
TLCGlobals.reset();
UniqueString.initialize();
RandomEnumerableValues.reset();
```

---

### 4. tlc-multi-run-test-design
**When to use**: Designing comprehensive multi-run test sequences

**File**: `.claude/skills/tlc-multi-run-test-design/SKILL.md`

**Capabilities**:
- Plan multi-run test patterns
- Design state capture at checkpoints
- Verify object identity differences
- Structure test assertions

**Pattern**: Run ModelA → Run ModelB → Reset → Run ModelC

---

### 5. tlc-debugging-state-issues
**When to use**: Debugging global state interference and persistence problems

**File**: `.claude/skills/tlc-debugging-state-issues/SKILL.md`

**Capabilities**:
- Diagnostic output techniques
- State snapshots
- Object tracking
- Memory address inspection
- Common issue solutions

---

## YAML Frontmatter Structure

Each SKILL.md uses this required structure:

```yaml
---
name: skill-name-in-kebab-case
description: Brief description of what this skill does and when to use it. (max 1024 chars)
---

# Skill Title

## Instructions
Step-by-step guidance for Claude

## Examples
Concrete examples of using this skill
```

**Requirements**:
- `name`: lowercase, hyphens only, max 64 chars
- `description`: Both what it does AND when to use it, max 1024 chars
- Must include trigger terms (keywords for auto-discovery)

## How Claude Uses These Skills

1. **Auto-discovery**: Claude reads `description` fields
2. **Trigger matching**: Claude activates when your request matches the description
3. **You don't explicitly invoke**: Skills activate automatically
4. **Progressive disclosure**: Claude reads files only when needed

## Example: How a Skill Gets Triggered

**Your request**: "I need to run the TLC test and check the results"

**Claude's thinking**: 
- This mentions "run" and "test" and "results"
- The `tlc-test-execution` skill description mentions "Execute TLC model-checking tests"
- Skill matches! Load and use it.

## Testing Skills

After creating a Skill, test it by asking Claude:

```
What Agent Skills are available?
```

Or test a specific Skill with a request that matches its description:

```
Can you help me create a new TLA+ model?
```

Claude should activate `tla-model-creation` if your request clearly involves model creation.

## Best Practices Applied

✅ **Skills are focused**: Each skill does ONE thing  
✅ **Descriptions are specific**: Include both what and when  
✅ **Examples are concrete**: Show real usage  
✅ **Instructions are clear**: Step-by-step guidance  
✅ **Trigger terms included**: Keywords for discovery  
✅ **Requirements documented**: What Claude needs  

## Integration with Documentation

- **AGENTS.md**: How AI models should work with the codebase
- **.claude/skills/**: Formal skill definitions for auto-discovery
- **INVESTIGATION_REPORT.md**: Technical deep-dive
- **INDEX.md**: Quick navigation guide

Skills are the programmatic interface for AI models, while docs are for humans.

## Usage in Claude Code

1. Clone/pull the repository
2. Skills are auto-discovered from `.claude/skills/`
3. Ask Claude Code a question that matches a skill description
4. Claude autonomously uses the appropriate skill

Example:
```
claude@project: Can you run the TLC test and show me the results?
```

Claude will automatically use `tlc-test-execution` skill!

## File Locations

From project root:
```
.claude/skills/
├── tlc-test-execution/SKILL.md
├── tla-model-creation/SKILL.md
├── tlc-global-state-management/SKILL.md
├── tlc-multi-run-test-design/SKILL.md
└── tlc-debugging-state-issues/SKILL.md
```

These are **project skills** (team-shared via git), not personal skills.

## Next Steps

1. Verify skills appear in Claude Code
2. Test with matching requests
3. Skills activate automatically
4. Use alongside AGENTS.md and other documentation

---

**Status**: Skills properly structured and ready for use
**Format**: Claude Code Agent Skills v1.0
**Discovery**: Automatic via description matching
