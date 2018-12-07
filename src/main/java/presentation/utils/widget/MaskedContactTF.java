package presentation.utils.widget;

public class MaskedContactTF extends MaskedTextField {
	
	private static final /*@ spec_public nullable @*/  String MASK_8DIGITS = "(##) ####-####";
	private static final /*@ spec_public nullable @*/  String MASK_9DIGITS = "(##) #####-####";
	
	public MaskedContactTF() {
		super(MASK_8DIGITS);
	}
	
	public void setContactPlainText(String contact) {
		this.adjustMask(contact.length());
		this.setPlainText(contact);
	}
	
	@Override
	public void replaceText(int start, int end, String newText){
		int selectionLength = (this.maskPositionToPlaintextPosition(end) - this.maskPositionToPlaintextPosition(start));
		int newPlainTextLength = this.getPlainText().length() - selectionLength + newText.length();
		this.adjustMask(newPlainTextLength);
		
		super.replaceText(start, end, newText);
	}
	
	@Override
	public void deleteText(int start, int end) {
		int selectionLength = (this.maskPositionToPlaintextPosition(end) - this.maskPositionToPlaintextPosition(start));
		int newPlainTextLength = this.getPlainText().length() - selectionLength;
		this.adjustMask(newPlainTextLength);
		
		super.deleteText(start, end);
	}
	
	private void adjustMask (int plainTextLength) {
		if (plainTextLength > 10) {
			this.setMask(MASK_9DIGITS);
		}
		else {
			this.setMask(MASK_8DIGITS);
		}
	}
}
