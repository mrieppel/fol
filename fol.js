// FOL Evaluator
//==============
//
// Copyright (c) 2012-2017 Michael Rieppel
//


// These are the global variables that store information about the model (domain and
// extensions for various lexical items)
var DOMAIN = [];
var CONSTANTS = {};
var SENTENCES = {};
var PREDICATES1 = {};
var PREDICATES2 = {};


// Denotation Constructors
//========================

// Below are constructor functions for the various different kinds of denotations. These 
// constructors generally take three arguments (s,f,v): s is the symbol to which the 
// denotation is assigned, f the formula the symbol is an immediate constituent of, and
// v a list of the predicate abstractors that the symbol is in the scope of.  
// The constructor then returns the appropriate denotation; this is a function which,
// inter alia, also sometimes stores the just-mentioned information via closures.
//
// Broadly, the semantic background theory is as follows.  Letting e be the type of 
// individuals, t the type of truth values, and g the type of assignment functions, the
// various lexical items denote functions of the following types:
//
// Variables: (g,e)
// Sentences: (g,t)
// 1-place predicates: ((g,e),(g,t))
// 2-place predicates: ((g,e),((g,e),(g,t)))
// Unary connective: ((g,t),(g,t))
// Binary connective: ((g,t),((g,t),(g,t)))
// Predicate abstractor: ((g,t),((g,e),(g,t))) i.e. takes sentence returns predicate
// Quantifier: (((g,e),(g,t)),(g,t)) i.e. takes predicate returns sentence
//
// However, there is a complication: those functions which are supposed to return a 
// boolean in actuality return an array with the relevant boolean value at the 0th
// index of the array, and other information in the rest of the array. This returned
// array is needed so that the program can compute not only the truth value of the
// sentence being evaluated, but also the entire history of that evaluation.
//
// Specifically: the 1th index contains the formula being evaluated, the 2th index
// contains the assignment function (a JavaScript object) relative to which the formula 
// is being evaluated,  and the 3rd index contain arrays corresponding to evaluations
// further down the evaluation process.
//
// For the record, I here include some commented-out denotation constructors showing what
// they would look like without these complications:
// 
// function mk1prDen(s) { // for 1-place predicates
// 	var ext = getExt(s);
// 	return function (x) {
// 		return function (g) {
// 			return isin(x(g),ext);
// 		}
// 	}	
// }
// 
// function mkCnjDen() { // for the conjunction operator
// 	return function (x) {
// 		return function (y) {
// 			return function (g) {
// 				return x(g)&&y(g);
// 			}
// 		}
// 	}
// }
// 
// function mkUqDen() { // for the universal quantifier
// 	return function(p) {
// 		return function (g) {
// 			var tv = true;
// 			for(var i=0;i<DOMAIN.length;i++) {
// 				if(!((p(function (h) {return DOMAIN[i];}))(g))){tv = false;}
// 			}
// 			return tv.
// 		}
// 	}
// }


// (g,e)
function mkVarDen(s) {
	return function (g) {return g[s];}
}

// ((g,e),(g,t))
function mk1prDen(s,f,v) {
	var ext = get1Ext(s);
	return function (x) {
			return function (g) {
				var out = isin(x(g),ext);
				return [out,f,getRealG(g,v)];
			}
	}	
}

// ((g,e),((g,e),(g,t)))
function mk2prDen(s,f,v) {
	var ext = get2Ext(s);
	return function (x) {
		return function (y) {
			return function (g) {
				var out = isIn([x(g),y(g)],ext);
				return [out,f,getRealG(g,v)];
			}
		}
	}	
}

// ((g,e),((g,e),(g,t)))
function mkIdDen(s,f,v) {
	return function (x) {
		return function (y) {
			return function (g) {
				var out = x(g)===y(g);
				return [out,f,getRealG(g,v)];
			}
		}
	}	
}

// (g,t)
function mkSenDen(s,f,v) {
	var tv = getSenExt(s);
	return function(g) {
		return [tv,f,getRealG(g,v)];
	}


}

// ((g,t),(g,t))
function mkNegDen(s,f,v) {
	return function (x) {
			return function (g) {
				var xg = x(g);
				return [!xg[0],f,getRealG(g,v),xg];
			}
	}
}

// ((g,t),((g,t),(g,t)))
function mkCnjDen(s,f,v) {
	return function (x) {
			return function (y) {
				return function (g) {
					var xg = x(g);
					var yg = y(g);
					return [xg[0]&&yg[0],f,getRealG(g,v),xg,yg];
				}
			}
	}
}

// ((g,t),((g,t),(g,t)))
function mkDsjDen(s,f,v) {
	return function (x) {
		return function (y) {
			return function (g) {
				var xg = x(g);
				var yg = y(g);
				return [xg[0]||yg[0],f,getRealG(g,v),xg,yg];
			}
		}
	}
}

// ((g,t),((g,t),(g,t)))
function mkCndDen(s,f,v) {
	return function (x) {
		return function (y) {
			return function (g) {
				var xg = x(g);
				var yg = y(g);
				return [(!xg[0])||yg[0],f,getRealG(g,v),xg,yg];
			}
		}
	}
}

// ((g,t),((g,t),(g,t)))
function mkBicDen(s,f,v) {
	return function (x) {
		return function (y) {
			return function (g) {
				var xg = x(g);
				var yg = y(g);
				return [xg[0]===yg[0],f,getRealG(g,v),xg,yg];
			}
		}
	}
}

// (((g,e),(g,t)),(g,t))
function mkUqDen(s,f,v) {
	return function(p) {
		return function (g) {
			var tr = [];
			var tv = true;
			for(var i=0;i<DOMAIN.length;i++) {
				var foo = p(function (h) {return DOMAIN[i];})(g);
				if(!foo[0]) {tv = false;}
				tr = tr.concat([foo]);
			}
			return [tv,f,getRealG(g,v),tr];
		}
	}
}

// (((g,e),(g,t)),(g,t))
function mkEqDen(s,f,v) {
	return function(p) {
		return function (g) {
			var tr = [];
			var tv = false;
			for(var i=0;i<DOMAIN.length;i++) {
				var foo = p(function (h) {return DOMAIN[i];})(g);
				if(foo[0]) {tv = true;}
				tr = tr.concat([foo]);
			}
			return [tv,f,getRealG(g,v),tr];
		}
	}
}

// ((g,t),((g,e),(g,t)))
function mkAbsDen(s) {
	return function (t) {
		return function (x) {
			return function (g) {
				g[s]=x(g);
				return t(g);
			}
		}
	}
}


function mkBinDen(c,f,v) {
	switch (c) {
		case '&' : return mkCnjDen(c,f,v);
		case 'v' : return mkDsjDen(c,f,v);
		case '>' : return mkCndDen(c,f,v);
		case '<>' : return mkBicDen(c,f,v);
	}
}

function get1Ext(p) {
	return PREDICATES1[p];
}

function get2Ext(p) {
	return PREDICATES2[p];
}

function getSenExt(p) {
	if(p==='#') {
		return false;
	} else {
		return SENTENCES[p];
	}
}

// Assignment, [Char] -> Assignment
// Takes an assignment function (a JavaScript object), and an array of variables, and 
// returns a "pruned" assignment that only stores information about assigned values
// for the variables in the provided array.
function getRealG(g,v) {
	var out = {};
	for(var i=0;i<v.length;i++) {
		out[v[i]] = g[v[i]];
	}
	return out;
}


// Some Array Comparison Functions
// ===============================

// checks if o is in array arr, where o is an int or array of ints
function isIn(o,arr) {
	for(var i=0;i<arr.length;i++) {
		if(arrEq(arr[i],o)) {
			return true;
			}
	}
	return false;
}

// checks ints, and Arrays of ints of any depth, for equality
function arrEq(ar1,ar2) {
	var out = true;
	if((Array.isArray(ar1) && Array.isArray(ar2)) && ar1.length==ar2.length) {
		for(var i=0;i<ar1.length;i++) {
			out = arrEq(ar1[i],ar2[i]) && out;
		}
		return out;
	}
	if(!(ar1 instanceof Array) && !(ar2 instanceof Array)) {
		return ar1==ar2;
	}
	return false;
}

// simpler membership function where o is not an array
function isin(o,ar) {
	return ar.indexOf(o)>=0;
}

// determines if array x is a subset (initial segment) of array y
function subset(x,y) {
	var out = false;
	for(var i=0;i<x.length;i++) {
		for(var j=0;j<y.length;j++) {
			if(x[i]===y[j]) {out = true;}
		}
		if(out) {out = false;} else {return false;}
	}
	return true;
}


// Interpretation
//===============

// Takes a tree as output by insertDen(), does functional application on the various
// denotations in the tree, and returns the output of those functional applications.  
// This output is a function that then takes a variable assignment and returns
// an array representation of the evaluation history on that assignment.
function interpret(t) {
	if(t[0]=='Q') {
		return t[2](t[3](interpret(t[4])));
	}
	if(t[0]=='U') {
		return t[2](interpret(t[3]));
	}
	if(t[0]=='B') {
		return t[3](interpret(t[2]))(interpret(t[4]));
	}
	if(t[0]=='0p') {
		return t[2];
	}
	if(t[0]=='1p') {
		return t[2](t[3]);
	}
	if(t[0]=='2p' || t[0]=='=') {
		return t[2](t[3])(t[4]);
	}
}


// Building a Tree Containing Denotations
//=======================================
// Tree, [Char] -> Tree
// Takes a parse tree as output by the parse() function, and an array tracking which 
// variable binders have been encountered in the tree so far,  and then substitutes 
// the appropriate denotations into the tree.  (Each denotation then has access to
// information about which variable binders it occurs in the scope of.)

function insertDen(t,v) {
	if(t[0]=='Q' && t[2]=='E') {
		return [t[0],t[1],mkEqDen('E',t[1],v),mkAbsDen(t[3]),insertDen(t[4],v.concat(t[3]))];
	}
	if(t[0]=='Q' && t[2]=='A') {
		return [t[0],t[1],mkUqDen('A',t[1],v),mkAbsDen(t[3]),insertDen(t[4],v.concat(t[3]))];
	}
	if(t[0]=='U') {
		return [t[0],t[1],mkNegDen('~',t[1],v),insertDen(t[3],v)];
	}
	if(t[0]=='B') {
		return [t[0],t[1],insertDen(t[2],v),mkBinDen(t[3],t[1],v),insertDen(t[4],v)];
	}
	if(t[0]=='0p') {
		if(SENTENCES[t[2]]===undefined) {
			throw 'ERROR: cannot evaluate. The loaded model contains no extension for the sentence letter '+t[2]+'.';
		} else {return [t[0],t[1],mkSenDen(t[2],t[1],v)];}
	}
	if(t[0]=='1p') {
		if(PREDICATES1[t[2]]===undefined) {
			throw 'ERROR: cannot evaluate.  The loaded model contains no extension for the 1-place predicate '+t[2]+'.';
		}
		var ck = defined(v,[t[3]]);
		if(!ck[0]) {
			throw 'ERROR: cannot evaluate. The symbol '+ck[1]+' occurs in the formula you entered as either a constant that has no extension in the loaded model, or as an unbound variable.';
		} else {return [t[0],t[1],mk1prDen(t[2],t[1],v),mkVarDen(t[3])];}
	}
	if(t[0]=='2p') {
		if(PREDICATES2[t[2]]===undefined) {
			throw 'ERROR: cannot evaluate. The loaded model contains no extension for the 2-place predicate '+t[2]+'.';
		} 
		var ck = defined(v,[t[3],t[4]]);
		if(!ck[0]) {
			throw 'ERROR: cannot evaluate. The symbol '+ck[1]+' occurs in the formula you entered as either a constant that has no extension in the loaded model, or as an unbound variable.';
		} else {return [t[0],t[1],mk2prDen(t[2],t[1],v),mkVarDen(t[3]),mkVarDen(t[4])];}
	} 
	if(t[0]=='=') {
		var ck = defined(v,[t[3],t[4]]);
		if(!ck[0]) {
			throw 'ERROR: cannot evaluate. The symbol '+ck[1]+' occurs in the formula you entered as either a constant that has no extension in the loaded model, or as an unbound variable.';
		} else {return [t[0],t[1],mkIdDen(t[2],t[1],v),mkVarDen(t[3]),mkVarDen(t[4])];}
	} else throw "ERROR: can't identify tree in insertDen(). t[0] is:"+t[0];
	
	function defined(v,ar) {
		for(var i=0;i<ar.length;i++) {
			if(v.indexOf(ar[i])<0 && CONSTANTS[ar[i]]===undefined) {
				return [false,ar[i]];
			}
		}
		return [true,[]];
	}
}


// FORMULA PARSING CODE
//====================

/* THE GRAMMAR
S ::= Q S | U S | '(' S B S ')' | A
Q ::= '(A' V ')' | '(E' V ')'
U ::= '~'
B ::= '&' | 'v' | '>' | '<>'
A ::= '#' | T=T | P | P T | P T T | P T T T ...
P ::= 'A' | 'B' | 'C' | 'D' | ...
T ::= C | V
C :: = 'a' | 'b' | 'c' | 'd'
V :: = 'w' | 'x' | 'y' | 'z' 
*/


// String -> Tree
// Takes a string and if it's a wff, returns a parse tree of the string, otherwise
// returns an empty array.  The first element of any parse tree is always an identifier
// of the type of wff (Q = quantifier wff, B = binary connective wff, P = predicational
// wff etc.) the second element is the wff that's being parsed, and the rest
// is the actual parsing. E.g. "Ax(~Fx&Gx)" parses to:
// [Q,Ax(~Fx&Gx),A,x,[B,(~Fx&Gx),[U,~Fx,~,[P,Fx,F,x]],&,[P,Gx,G,x]]]

function parse(s) {
	s = s.replace(/ /g,'');
	if(s=='') {return [];}
	var s1 = [];
	var s2 = [];
	if(isQ(s)) {
		s1 = parse(s.substring(2));
		return s1.length ? ['Q',s,s.charAt(0),s.charAt(1),s1] : [];
	}
	if(isU(s[0])) {
		s1 = parse(s.substring(1));
		return s1.length ? ['U',s,s[0],s1] : [];
	}
	if(s[0] =='(' && s[s.length-1]==')') {
		var a = gSub(s);
		if(a.indexOf(undefined)>=0 || a.indexOf('')>=0) {
			return [];
		} else {
			s1 = parse(a[0]);
			s2 = parse(a[2]);
			if(s1.length && s2.length) {
				return ['B',s,s1,a[1],s2];
			} else {return [];}
		}
	}
	if(isAt(s)) {
		if(s.length==1) {
			return ['0p',s,s];
		}
		if(s.length==2) {
			return ['1p',s,s[0],s[1]];
		} 
		if(s.length==3 && s[1]=='=') {
			return ['=',s,s[1],s[0],s[2]];
		}
		if(s.length==3) {
			return ['2p',s,s[0],s[1],s[2]];
		} else {return [];} // not allowing n-place predicates for n>2
	
	} else {return [];}
}

// String -> Bool
// Determines if s is an atomic wff
function isAt(s) {
	var pr = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
	if(s.length==1 && s==='#') {return true;}
	if(s.length==3 && isT(s[0]) && s[1]=='=' && isT(s[2])) {
		return true;
	}
	if(pr.indexOf(s[0])>=0) {
	 	if(s.length==1) {
	 		return true;
	 	} else {
	 		for(var i=1;i<s.length;i++) {
	 			if(!isT(s[i])) {
	 				return false;
	 			}
	 		}
	 		return true;
	 	}
		
	} else {return false;}
}

// String -> Bool
// Determines if s begins with a quantifier
function isQ(s) {
	var q = ['E','A'];
	if(s.length>2 && q.indexOf(s[0])>=0 && isV(s[1]) && !isB(s[2]) && !(isV(s[2]) && s[3]!=='=')) {
		return true;
	} else {return false;}
}

// String -> Bool
// Determines if s begins with a unary connective
function isU(s) {
	var u = ['~'];
	for(var i=0;i<u.length;i++) {
		if(s.indexOf(u[i])==0) {return true;}
	}
	return false;
}

// String -> [String]
// takes a string beginning with '(' and ending with ')', and determines if there is a
// binary connective enclosed only by the outermost parentheses.  If so, returns an array
// with the string to the left and the string to the right of the binary connective; 
// otherwise returns an array of three undefined's.
function gSub(s) {
	var stk = [];
	var l = 0;
	for(var i=0;i<s.length;i++) {
		if(s[i]=='(') {
			stk.push('(');
		} else if(s[i]==')' && stk.length>0) {
			stk.pop();
		} else if(stk.length==1 && (l = isB(s.substring(i)))>0) {
			return [s.substring(1,i),s.substring(i,i+l),s.substring(i+l,s.length-1)];
		}	
	}
	return [undefined,undefined,undefined];
}

// String -> Int
// takes a string and determines if it begins with a binary connective.  If so, returns
// the length of the connective, otherwise returns 0.
function isB(s) {
	var bc = ['&','v','>','<>'];
	for(var i=0;i<bc.length;i++) {
		if(s.indexOf(bc[i]) == 0) {
			return bc[i].length;
		}
	}
	return 0;
}

// Char -> Bool
// Determines if c is a term
function isT(c) {
	return (isC(c) || isV(c));
}

// Char -> Bool
// Determines if c is a variable.
function isV(c) {
	return 'abcdefghijklmnopqrstuwxyz'.indexOf(c)>=0;
}

// Char -> Bool
// Determines if c is a constant
function isC(c) {
	return 'abcdefghijklmnopqrstuwxyz'.indexOf(c)>=0;
}