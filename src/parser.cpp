/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator , denominator));
    //TODO: complete the rational parser
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());

    if (id == nullptr) {
        vector<Expr> operands;
        for (auto & s : stxs) {
            operands.emplace_back(s->parse(env));
        }
        return Expr(new Apply(operands[0] , vector<Expr>(operands.begin()+1 , operands.end())));
        //TODO: TO COMPLETE THE LOGIC
    }else{
    string op = id->s;
    if (find(op, env).get() != nullptr) {

        //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1 ; i < stxs.size() ; ++i) {
            parameters.emplace_back(stxs[i]->parse(env));
        }
        //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
        
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() <= 1)
                throw RuntimeError("+ requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Plus(parameters[0] , parameters[1]));
            return Expr(new PlusVar(parameters));
        } else if (op_type == E_MINUS) {
            if (parameters.size() <= 1)
                throw RuntimeError("- requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Minus(parameters[0] , parameters[1]));
            return Expr(new MinusVar(parameters));
        } else if (op_type == E_MUL) {
            if (parameters.size() <= 1)
                throw RuntimeError("* requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Mult(parameters[0] , parameters[1]));
            return Expr(new MultVar(parameters));
        } else if (op_type == E_DIV) {
            if (parameters.size() <= 1)
                throw RuntimeError("/ requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Div(parameters[0] , parameters[1]));
            return Expr(new DivVar(parameters));
        }  else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            if (parameters.size() <= 1)
                throw RuntimeError("< requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Less(parameters[0] , parameters[1]));
            return Expr(new LessVar(parameters));
            //TODO: TO COMPLETE THE LOGIC
        } else if (op_type == E_LE) {
            if (parameters.size() <= 1)
                throw RuntimeError("<= requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new LessEq(parameters[0] , parameters[1]));
            return Expr(new LessEqVar(parameters));
            //TODO: TO COMPLETE THE LOGIC
        } else if (op_type == E_EQ) {
            if (parameters.size() <= 1)
                throw RuntimeError("== requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Equal(parameters[0] , parameters[1]));
            return Expr(new EqualVar(parameters));
            //TODO: TO COMPLETE THE LOGIC
        } else if (op_type == E_GE) {
            if (parameters.size() <= 1)
                throw RuntimeError(">= requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new GreaterEq(parameters[0] , parameters[1]));
            return Expr(new GreaterEqVar(parameters));
            //TODO: TO COMPLETE THE LOGIC
        } else if (op_type == E_GT) {
            if (parameters.size() <= 1)
                throw RuntimeError("> requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Greater(parameters[0] , parameters[1]));
            return Expr(new GreaterVar(parameters));
            //TODO: TO COMPLETE THE LOGIC
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else {
            throw RuntimeError("Unknown primitive operator: " + op);
            //TODO: TO COMPLETE THE LOGIC
        }
    }

    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
    	    case E_BEGIN:
    	        break;
    	    case E_QUOTE:
    	        break;
    	    case E_IF:
    	        break;
    	    case E_COND:
    	        break;
    	    case E_LAMBDA:
    	        break;
    	    case E_DEFINE:
    	        break;
    	    case E_LET:
    	        break;
    	    case E_LETREC:
    	        break;
    	    case E_SET:
    	        break;
			//TODO: TO COMPLETE THE reserve_words PARSER LOGIC
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    //default: use Apply to be an expression
    //TODO: TO COMPLETE THE PARSER LOGIC
}
}
