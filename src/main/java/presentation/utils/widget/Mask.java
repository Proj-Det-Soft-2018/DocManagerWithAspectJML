package presentation.utils.widget;

/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/**
 * @author gbfragoso
 * 
 */
public class Mask {
    
    private final char maskChar;
    private final boolean literal;
    private char value;
    private boolean placeholder;
    
    public Mask (char maskChar, boolean literal, boolean placeholder) {
        this.maskChar = maskChar;
        this.literal = literal;
        this.placeholder = placeholder;
    }
    
    public Mask (char value, char maskChar, boolean literal, boolean placeholder) {
        this.value = value;
        this.maskChar = maskChar;
        this.literal = literal;
        this.placeholder = placeholder;
    }
    
    public char getMask(){
        return this.maskChar;
    }
    
    public char getValue(){
        return this.value;
    }
    
    public void setValue(char value){
        this.value = value;
    }
    
    public boolean isLiteral(){
        return this.literal;
    }
    
    public boolean isPlaceholder(){
        return this.placeholder;
    }

    public void setPlaceholder(boolean placeholder) {
        this.placeholder = placeholder;
    }
}
