// Gets user's input formula, interprets it on model, and prints out the evaluation
// history to the sout div.
function processFormula() {
	if(DOMAIN.length==0) {
		return outputErr('ERROR: you must first load a model.','sout');
	}
	var s = document.getElementById('sin').value;
	s = s.replace(/ /g,'');
	if(s=='') {
		return outputErr('ERROR: you have not entered a string.','sout');
	}
	var t = parse(s);
	if(t.length==0) {
		t = parse('('+s+')');
		if(t.length==0) {
			return outputErr('ERROR: Malformed formula.','sout');
		}
	}
	try {
		var l = insertDen(t,[]);
		var i = interpret(l)(getG());
		var out = printout(i,0);
		out = i[1]+" is "+i[0]+" on this model\n\n \nEvaluation History:\n-------------------\n\n"+out;
	} catch(err) {
		outputErr(err,'sout');
		return;
	}
	document.getElementById('sout').innerHTML = '<pre>'+out+'</pre>';
	
	function getG() {
		var x = Object.keys(CONSTANTS);
		var out = {};
		for(var i=0;i<x.length;i++) {
			out[x[i]] = CONSTANTS[x[i]];
		}
		return out;
	}
}

// Array, Int -> String
// Takes an evaluation tree as returned by interpret(), together with an int representing
// the depth of the current tree, and returns a string representation of the evaluation 
// history.
function printout(a,d) {
	if(Array.isArray(a[0])) {
		var out = "";
		for(var i=0;i<a.length;i++) {
			out = out+printout(a[i],d);
		}
		return out;
	}
	if(a.length==3) {
		return getspaces(d)+a[1]+" is "+a[0]+" on "+JSON.stringify(a[2])+"\n";
	}
	if(a.length==4) {
		return getspaces(d)+a[1]+" is "+a[0]+" on "+JSON.stringify(a[2])+"\n"+printout(a[3],d+1);
	}
	if(a.length==5) {
		return getspaces(d)+a[1]+" is "+a[0]+" on "+JSON.stringify(a[2])+"\n"+printout(a[3],d+1)+printout(a[4],d+1);
	}
}

function getspaces(d) {
	var out = "";
	for(var i=0;i<d;i++) {
		out = out+"      ";
	}
	return out;
}


// Generate Model From User Input
// ================================

// Attempts to load model entered by user.
function loadModel() {
	clearGlobals();
	var dm = document.getElementById('d').value.split(' ').join('');
	try {
		mkMdl('domain',dm);
	} catch(err) {
		outputErr(err,'mout');
		return;
	}
	var e = document.getElementById('model');
	var lis = e.getElementsByTagName('li');
	for(var i=1;i<lis.length;i++) {
		var l = document.getElementById(i+'l').value.split(' ').join('');
		var r = document.getElementById(i+'r').value.split(' ').join('');
		if(!l=='') {
			try {
				mkMdl(l,r);
			} catch(err) {
				outputErr(err,'mout');
				return;
			}
		}
	}
	printModel(model);
}


// Adds the information from the user's model to the global variables storing the model
// information (domain, predicate extensions etc.)
function mkMdl(n,s) {
	if(n=='domain') {
		if(s.length==0) {
			throw 'ERROR: domain must be nonempty';
		}
		if(!ck1Ext(s)) {
			throw 'ERROR: domain must consist of a list of integers.';
		}
		DOMAIN = s.split(',').map(function (x) {return parseInt(x);});
		return DOMAIN.sort();
	}
	if(n.length==1 && 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.indexOf(n)>=0) {
		if(s=='T') {
			SENTENCES[n] = true;
			return;
		}
		if(s=='F') {
			SENTENCES[n] = false;
			return;
		}
		if(s=='') {
			PREDICATES1[n] = [];
			PREDICATES2[n] = [];
			return;
		}
		if(ck1Ext(s)) {
			var ext = [];
			if(s.length>0) {
				ext = s.split(',').map(function (x) {return parseInt(x);})
			}
			if(!subset(ext,DOMAIN)) {
				throw 'ERROR: extensions for 1-place predicates must be subsets of the domain.';
			}
			PREDICATES1[n] = ext;
			return;
		}
		if(ck2Ext(s)) {
			var ext = g2Ext(s);
			for(var j=0;j<ext.length;j++) {
				if(!subset(ext[j],DOMAIN)) {
					throw 'ERROR: extensions of 2-place predicates must be pairs of domain elements.';
				}
			}
			PREDICATES2[n] = ext;
			return;
		} else {
			throw 'ERROR: the extension entered for '+n+' is not recognized.';
		}
	} 
	
	if(isC(n)) {
		var ext = parseInt(s);
		if(s<0) {
			throw 'ERROR: the extension of the individual constant '+n+' must be a positive integer.';
		}
		if(!isin(ext,DOMAIN)) {
			throw 'ERROR: the extension of the individual constant '+n+' must be an element of the domain.';
		}
		CONSTANTS[n] = ext;
		
	} else {
		throw 'ERROR: the symbol '+n+' in the model specification is not a recognized lexical item.';
	}
	
}

// checks if string is a well-formed representation of a 1-place predicate extension
function ck1Ext(s) {
	if(s.length==0) {return true;}
	if(!isInt(s.charAt(0))) {return false;}
	for(var i=0;i<s.length;i++) {
		if(isInt(s.charAt(i))) {
			continue;
		} else if(s.charAt(i)==',' && isInt(s.charAt(i+1))) {
			continue;
		} else {return false;}
	}
	return true;
}

// checks if string is a well-formed representation of a 2-place predicate extension
function ck2Ext(s) {
	if(s.length==0) {return true;}
	if(!(s.charAt(0)=='(')) {return false;}
	var stk = [','];
	for(var i=0;i<s.length;i++) {
		if(s.charAt(i)=='(' && stk[stk.length-1]==',') {
			stk = ['('];
			continue;
		}
		if(s.charAt(i)==',' && stk[stk.length-1]=='i' && stk[stk.length-2]=='(') {
			stk.push(',');
			continue;
		}
		if(s.charAt(i)==')' && stk[stk.length-1]=='i' && stk[stk.length-2]==',') {
			stk = [];
			continue;
		} 
		if(s.charAt(i)==',' && stk.length==0) {
			stk.push(',');
			continue;
		}
		if(isInt(s.charAt(i))) {
			if(stk[stk.length-1]=='i') {continue;} else {stk.push('i');}
		} else {return false;}
	}
	if(stk.length==0) {return true;} else {return false;}
}

// produces an array of pairs from a string representation of a 2-place extension
function g2Ext(s) {
	var out = [];
	var sub = '';
	while(s.length>0) {
			var l = s.substring(1,s.indexOf(','));
			var r = s.substring(s.indexOf(',')+1,s.indexOf(')'));
			out.push([parseInt(l),parseInt(r)]);
			if(s.substring(1,s.length).indexOf('(')==-1) {
				break;
			} else {
			s = s.substring(s.indexOf(')')+2,s.length);	
			}
	}
	return out;
}

// determines if char x represents an int
function isInt(x) {
	return parseInt(x)>=0;
}

// Clears the model from the global variables
function clearGlobals() {
	DOMAIN = [];
	CONSTANTS = {};
	SENTENCES = {};
	PREDICATES1 = {};
	PREDICATES2 = {};
}


// Clears the model from the html interface
function clearModel() {
	clearGlobals();
	document.getElementById('mout').innerHTML = '';
	document.getElementById('sout').innerHTML = '';
	document.getElementById('d').value = '';
	
	var e = document.getElementById('model');
	var lis = e.getElementsByTagName('li').length;
	
	for(var i=1;i<lis;i++) {
		var x = document.getElementById(i+'l');
		x.value = '';
		document.getElementById(i+'r').value = '';
		if(i==4) {
			var span = document.getElementById('add4');
			span.innerHTML = '';
			var newbutton = document.createElement('input');
			newbutton.type = 'button';
			newbutton.value = '+';
			newbutton.className = 'addbutton';
			newbutton.onclick = function() {return addLine(5);};
			span.appendChild(newbutton);
		}	
		if(i>4) {
			document.getElementById('model').removeChild(x.parentNode);
		}
	}
}

// Loads sample model
function loadSample() {
	document.getElementById('d').value = '1,2,3';
	document.getElementById('1l').value = 'R';
	document.getElementById('1r').value = '(1,1),(1,2),(1,3),(2,2),(3,3)';
	document.getElementById('2l').value = 'F';
	document.getElementById('2r').value = '1,3';
 	document.getElementById('3l').value = 'a';
 	document.getElementById('3r').value = '1';
 	document.getElementById('4l').value = 'P';
 	document.getElementById('4r').value = 'F';
	loadModel();
}

// Prints an error to the html element with the given id
function outputErr(err,id) {
	var outStr = '<p style=\'color:red;\'>' + err + '</p>';
	document.getElementById(id).innerHTML = outStr;
}

// Prints the loaded model to the html interface.
function printModel(m) {
	var outStr = '<p><b>Loaded Model</b></p>';
	outStr += '<ul style="list-style:none;padding:0px;"><li>Domain: '+JSON.stringify(DOMAIN)+'</li>';
	
	var preds2 = Object.keys(PREDICATES2);
	if(preds2.length>0) {
		for(var i=0;i<preds2.length;i++) {
			outStr += '<li>'+preds2[i]+': '+mkSeq(JSON.stringify(PREDICATES2[preds2[i]]))+'</li>';
		}
	}
	var preds1 = Object.keys(PREDICATES1);
	if(preds1.length>0) {
		for(var i=0;i<preds1.length;i++) {
			if(preds2.indexOf(preds1[i])>=0) {
				continue;
			} else {outStr += '<li>'+preds1[i]+': '+JSON.stringify(PREDICATES1[preds1[i]])+'</li>';}
		}
	}
	var cons = Object.keys(CONSTANTS);
	if(cons.length>0) {
		for(var i=0;i<cons.length;i++) {
			outStr += '<li>'+cons[i]+': '+CONSTANTS[cons[i]]+'</li>';
		}
	}
	var sens = Object.keys(SENTENCES);
	if(sens.length>0) {
		for(var i=0;i<sens.length;i++) {
			outStr += '<li>'+sens[i]+': '+SENTENCES[sens[i]]+'</li>';
		}
	}
	document.getElementById('mout').innerHTML = outStr+'</ul>';
	
	// Takes a JSON.stringify() representation of an array of arrays and changes square
	// brackets into parentheses
	function mkSeq(s) {
		s = s.substring(1,s.length-1);
		s = s.replace(/\[/g,'(');
		s = s.replace(/\]/g,')');
		return '['+s+']';
	}
}


// Adds another line to the "model input" fields in the html interface
function addLine(n) {
	var newli = document.createElement('li');
	
	var newin1 = document.createElement('input');
	newin1.type = 'text';
	newin1.className = 'inL'
	newin1.id = n+'l';
	newli.appendChild(newin1);
	
	var newin2 = document.createElement('input');
	newin2.type = 'text';
	newin2.className = 'inR'
	newin2.id = n+'r';
	newli.appendChild(newin1);
	newli.appendChild(newin2);
	
	var newspan = document.createElement('span');
	newspan.id = 'add'+n;
	var newbutton = document.createElement('input');
	newbutton.type = 'button';
	newbutton.value = '+';
	newbutton.className = 'addbutton';
	newbutton.onclick = function() {return addLine(n+1);};
	newspan.appendChild(newbutton);
	newli.appendChild(newspan);
	
	document.getElementById('add'+(n-1)).innerHTML = "";
	document.getElementById('model').appendChild(newli);
}