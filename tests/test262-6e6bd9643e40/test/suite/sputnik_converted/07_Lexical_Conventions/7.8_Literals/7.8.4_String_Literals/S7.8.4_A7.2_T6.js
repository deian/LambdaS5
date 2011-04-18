// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
 * @name: S7.8.4_A7.2_T6;
 * @section: 7.8.4;
 * @assertion: UnicodeEscapeSequence :: u HexDigit (one, two or three time) is incorrect;
 * @description: :: HexDigit :: A;	
 * @negative
*/


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S7.8.4_A7.2_T6",

path: "7.8.4",

description: ":: HexDigit :: A",

test: function testcase() {
  try {
     (function() {
         eval("//CHECK#1\r\n\"\\uAAA\"\r\n") })();
   } catch (__e__) {return true  /* failure is success */};
   return false /* but success is failure */
 }
});

