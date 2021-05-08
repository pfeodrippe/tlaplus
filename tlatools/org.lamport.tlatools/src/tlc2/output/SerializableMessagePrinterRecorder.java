package tlc2.output;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import tlc2.tool.TLCStateInfo;

public class SerializableMessagePrinterRecorder implements IMessagePrinterRecorder {

    // Store messages from the recorder subscription.
    private final Map<Integer, List<Object>> records = new HashMap<Integer, List<Object>>();

    @Override
	public void record(int code, Object... objects) {
        if(!records.containsKey(code)) {
			records.put(code, new ArrayList<Object>());
		}

        final TLCStateInfo stateInfo;
        switch (code) {
            // Trace step.
            case EC.TLC_STATE_PRINT2:
                stateInfo = (TLCStateInfo) objects[0];
                // Stringify stateInfo and add `info` to `objects[2]`.
                records.get(code).add(new Object[] {stateInfo.toString(), objects[1], stateInfo.info});
                break;

            // Stuttering final state.
            case EC.TLC_STATE_PRINT3:
                stateInfo = (TLCStateInfo) objects[0];
                // Stringify stateInfo.
                // `state` may be `null`, which would make `stateInfo.toString()` throw an exception.
                if (stateInfo.state == null) {
                    records.get(code).add(new Object[] {"", objects[1]});
                } else {
                    records.get(code).add(new Object[] {stateInfo.toString(), objects[1]});
                }
                break;

            default:
                records.get(code).add(objects);
                break;
        }
    }

    public void serializeTo(String filePath) {
        try {
            FileOutputStream fileOut = new FileOutputStream(filePath);
            ObjectOutputStream out = new ObjectOutputStream(fileOut);
            out.writeObject(this.records);
            out.close();
        } catch (IOException i) {
            i.printStackTrace();
        }
    }

}