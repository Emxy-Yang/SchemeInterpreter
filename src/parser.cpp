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
        vector<Expr> operands;
        for (auto & s : stxs) {
            operands.emplace_back(s->parse(env));
        }
        return Expr(new Apply(operands[0] , vector<Expr>(operands.begin()+1 , operands.end())));
        //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
    }
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1 ; i < stxs.size() ; ++i) {
            parameters.emplace_back(stxs[i]->parse(env));
        }
        //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
        auto v1 = Expr (new RationalNum(1,1));
    	auto v0 = Expr (new RationalNum(0,1));
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 0)
                return Expr(new Plus(v0,v0));
        	if (parameters.size() == 1) {
        		return parameters[0];
        	}
            if (parameters.size() == 2)
                return Expr(new Plus(parameters[0] , parameters[1]));
            return Expr(new PlusVar(parameters));
        } else if (op_type == E_MINUS) {
            if (parameters.size() < 1)
                throw RuntimeError("- requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Minus(parameters[0] , parameters[1]));
        	if (parameters.size() == 1) {
        		return Expr(new Minus(v0 , parameters[0]));
        	}
            return Expr(new MinusVar(parameters));
        } else if (op_type == E_MUL) {
            if (parameters.size() == 0)
            	return Expr(new Mult(v1,v1));
            if (parameters.size() == 2)
                return Expr(new Mult(parameters[0] , parameters[1]));
        	if (parameters.size() == 1) {
        		return parameters[0];
        	}
            return Expr(new MultVar(parameters));
        } else if (op_type == E_DIV) {
            if (parameters.size() < 1)
                throw RuntimeError("/ requires at least two argument");
            if (parameters.size() == 2)
                return Expr(new Div(parameters[0] , parameters[1]));
        	if (parameters.size() == 1) {
        		return Expr(new Div(v1 , parameters[0]));
        	}
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
        }else if (op_type == E_CAR) {
        	if (parameters.size() != 1)
        		throw RuntimeError("car requires exactly 1 argument");
        	return Expr(new Car(parameters[0]));
        }else if (op_type == E_CDR) {
        	if (parameters.size() != 1)
        		throw RuntimeError("cdr requires exactly 1 argument");
        	return Expr(new Cdr(parameters[0]));
        }else if (op_type == E_CONS) {
        	if (parameters.size() != 2)
        		throw RuntimeError("cons requires exactly 2 argument");
        	return Expr(new Cons(parameters[0] , parameters[1]));
        }else if (op_type == E_EQQ) {
        	if (parameters.size() != 2)
        		throw RuntimeError("eq? requires exactly 2 argument");
        	return Expr(new IsEq(parameters[0] , parameters[1]));
        }else if (op_type == E_BOOLQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("boolean? requires exactly 1 argument");
        	return Expr(new IsBoolean(parameters[0]));

        } else if (op_type == E_INTQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("number? requires exactly 1 argument");
        	return Expr(new IsFixnum(parameters[0]));

        } else if (op_type == E_NULLQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("null? requires exactly 1 argument");
        	return Expr(new IsNull(parameters[0]));

        } else if (op_type == E_PAIRQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("pair? requires exactly 1 argument");
        	return Expr(new IsPair(parameters[0]));

        } else if (op_type == E_PROCQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("procedure? requires exactly 1 argument");
        	return Expr(new IsProcedure(parameters[0]));

        } else if (op_type == E_SYMBOLQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("symbol? requires exactly 1 argument");
        	return Expr(new IsSymbol(parameters[0]));

        } else if (op_type == E_LISTQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("list? requires exactly 1 argument");
        	return Expr(new IsList(parameters[0]));

        } else if (op_type == E_STRINGQ) {
        	if (parameters.size() != 1)
        		throw RuntimeError("string? requires exactly 1 argument");
        	return Expr(new IsString(parameters[0]));
        }else if (op_type == E_EXIT) {
        	if (parameters.size() != 0)
        		throw RuntimeError("exit requires exactly 0 argument");
	        return Expr(new Exit());
        }else if (op_type == E_VOID) {
        	if (parameters.size() != 0)
        		throw RuntimeError("void requires exactly 0 argument");
        	return Expr(new MakeVoid());
        }else if (op_type == E_DISPLAY) {
        	if (parameters.size() != 1)
        		throw RuntimeError("Dispaly requires exactly 1 argument");
	        return Expr(new Display(parameters[0]));
        }
    	else {
            throw RuntimeError("Unknown primitive operator: " + op);
            //TODO: TO COMPLETE THE LOGIC
        }
    }

    if (reserved_words.count(op) != 0) {
    	switch (reserved_words[op]) {
    	    case E_BEGIN: {
    	        vector<Expr> BeginExpr;
    	        for (size_t i = 1; i < stxs.size(); ++i) {
    	            BeginExpr.push_back(stxs[i]->parse(env));
    	        }
    	        return Expr(new Begin(BeginExpr));
    	        break;
    	    }
    	    case E_QUOTE: {
    	        if (stxs.size() != 2) {
    	            throw RuntimeError("quote requires exactly 1 argument");
    	        }
    	        return Expr(new Quote(stxs[1]));
    	        break;
    	    }
    	    case E_IF: {
    	        vector<Expr> IfExpr;
    	        if (stxs.size() != 4) {
    	            throw RuntimeError("if requires exactly 3 argument");
    	        }
    	        for (size_t i = 1; i < stxs.size(); ++i) {
    	            IfExpr.push_back(stxs[i]->parse(env));
    	        }
    	        return Expr(new If(IfExpr[0],IfExpr[1],IfExpr[2]));
    	        break;
    	    }
    	    case E_COND: {
    	        if (stxs.size() < 2) {
    	            throw RuntimeError("cond requires at least one clause");
    	        }

    	        std::vector<std::vector<Expr>> clauses;

    	        for (size_t i = 1; i < stxs.size(); ++i) {
    	            auto clauseList = dynamic_cast<List*>(stxs[i].get());
    	            if (!clauseList || clauseList->stxs.empty()) {
    	                throw RuntimeError("cond clause must be a non-empty list");
    	            }

    	            std::vector<Expr> parsedClause;

    	            SyntaxBase *predicateSyntax = clauseList->stxs[0].get();

    	            if (auto sym = dynamic_cast<SymbolSyntax*>(predicateSyntax)) {
    	                if (sym->s == "else") {
    	                    if (i != stxs.size() - 1) {
    	                        throw RuntimeError("else clause must be the last clause of cond");
    	                    }
    	                    parsedClause.push_back(Expr(new Var("else")));
    	                } else {
    	                    parsedClause.push_back(predicateSyntax->parse(env));
    	                }
    	            } else {
    	                parsedClause.push_back(predicateSyntax->parse(env));
    	            }

    	            if (clauseList->stxs.size() == 1) {
    	            } else {
    	                for (size_t j = 1; j < clauseList->stxs.size(); ++j) {
    	                    parsedClause.push_back(
                                clauseList->stxs[j]->parse(env)
                            );
    	                }
    	            }
    	            clauses.push_back(parsedClause);
    	        }

    	        return Expr(new Cond(clauses));
    	        break;
    	    }
    	    case E_LAMBDA: {
    	        if (stxs.size() < 3) {
    	            throw RuntimeError("lambda requires parameter list and a body");
    	        }

    	        std::vector<std::string> params;


    	        auto pList = dynamic_cast<List*>(stxs[1].get());
    	        if (!pList) {
    	            throw RuntimeError("lambda parameter list must be a list");
    	        }

    	        for (auto &p : pList->stxs) {
    	            auto psym = dynamic_cast<SymbolSyntax*>(p.get());
    	            if (!psym) {
    	                throw RuntimeError("lambda parameter must be a symbol");
    	            }
    	            params.push_back(psym->s);
    	        }


    	        // std::vector<Expr> bodies;
    	        // for (size_t i = 2; i < stxs.size(); ++i) {
    	        //     bodies.push_back(stxs[i]->parse(env));
    	        // }



    	    	return Expr(new Lambda(params,stxs[2]->parse(env)));
    	    }
    	    case E_DEFINE: {
    	    	if (stxs.size() != 3) {
    	    		throw RuntimeError("define need 2 params");
    	    	}
    	    	if (auto sym = dynamic_cast<SymbolSyntax*>(stxs[1].get())) {
    	    		string varName = sym->s;

    	    		Expr rhs = stxs[2]->parse(env);

    	    		return Expr(new Define(varName, rhs));
    	    	}

    	    	if (auto lst = dynamic_cast<List*>(stxs[1].get())) {

    	    		if (lst->stxs.empty()) {
    	    			throw RuntimeError("malformed define function syntax");
    	    		}

    	    		auto fnameSym = dynamic_cast<SymbolSyntax*>(lst->stxs[0].get());
    	    		if (!fnameSym) {
    	    			throw RuntimeError("function name must be a symbol");
    	    		}

    	    		string funcName = fnameSym->s;

    	    		vector<string> params;
    	    		for (size_t i = 1; i < lst->stxs.size(); ++i) {
    	    			auto psym = dynamic_cast<SymbolSyntax*>(lst->stxs[i].get());
    	    			if (!psym) {
    	    				throw RuntimeError("lambda parameter must be symbol");
    	    			}
    	    			params.push_back(psym->s);
    	    		}

    	    		// vector<Expr> bodyExprs;
    	    		// for (size_t i = 2; i < stxs.size(); ++i) {
    	    		// 	bodyExprs.push_back(stxs[i]->parse(env));
    	    		// }

    	    		Expr lam = Expr(new Lambda(params, stxs[2]->parse(env)));

    	    		return Expr(new Define(funcName, lam));
    	    	}

    	    	throw RuntimeError("malformed define expression");
	    	    break;
    	    }
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
