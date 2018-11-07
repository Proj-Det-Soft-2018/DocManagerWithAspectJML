package presentation.utils.widget;

public class DynamicMaskTextField extends MaskedTextField {

	private String originalMask;
	private boolean dynamic;
	private int origMaskOffset;
	
	public void setDynamic(boolean dynamic) {
		this.dynamic = dynamic;
		if (dynamic) {
			this.setMask(originalMask);
		}
	}

	public DynamicMaskTextField(String originalMask, int maskOffset) {
		super(originalMask);
		this.originalMask = originalMask;
		this.origMaskOffset = maskOffset;
		this.dynamic = true;
	}
	
	@Override
	public void replaceText(int start, int end, String newText){
		int selectionLength = (this.maskPositionToPlaintextPosition(end) - this.maskPositionToPlaintextPosition(start));
		int newPlainTextLength = this.getPlainText().length() - selectionLength + newText.length();
		if (this.dynamic) {
			this.adjustMask(newPlainTextLength);
		}
		super.replaceText(start, end, newText);
	}
	
	@Override
	public void deleteText(int start, int end) {
		int selectionLength = (this.maskPositionToPlaintextPosition(end) - this.maskPositionToPlaintextPosition(start));
		int newPlainTextLength = this.getPlainText().length() - selectionLength;
		if (this.dynamic) {
			this.adjustMask(newPlainTextLength);
		}
		super.deleteText(start, end);
	}
	
	public void adjustMask (int plainTextLength) {
		StringBuilder newMask = new StringBuilder(this.originalMask);
		int sufixLength = plainTextLength - this.origMaskOffset;
		for (int i = 0; i <= sufixLength; i++) {
			newMask.append("*");
		}
		this.setMask(newMask.toString());
	}
}
