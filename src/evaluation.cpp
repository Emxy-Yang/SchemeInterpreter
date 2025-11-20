/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> args;
    for (const auto& i : rands) {
        args.emplace_back(i->eval(e));
    }

    return evalRator(args);
    // TODO: TO COMPLETE THE VARIADIC CLASS
}

Value Var::eval(Assoc &e) { // evaluation of variable

    if (x.empty() || (isdigit(x[0]) || x[0] == '.' || x[0] == '@')) {
        throw RuntimeError("Invalid variable name: starts with invalid character");
    }

    const std::string forbidden_chars = "#'\"`";
    for (char c : x) {
        if (forbidden_chars.find(c) != std::string::npos) {
            throw RuntimeError("Invalid variable name: contains forbidden character '" + std::string(1, c) + "'");
        }
    }

    auto isNumeric = [](const std::string &s) -> bool {
        if (s.empty())
            return false;
        size_t i = 0;
        if (s[i] == '+' || s[i] == '-')
            i++; // Sign
        bool has_digit = false;
        bool has_dot = false;
        bool has_exponent = false;
        while (i < s.size()) {
            if (isdigit(s[i])) {
                has_digit = true;
            } else if (s[i] == '.') {
                if (has_dot || has_exponent)
                    return false;
                has_dot = true;
            } else if (s[i] == 'e' || s[i] == 'E') {
                if (has_exponent || !has_digit)
                    return false;
                has_exponent = true;
                if (++i >= s.size() || (!isdigit(s[i]) && s[i] != '+' && s[i] != '-')) {
                    return false;
                }
                if (s[i] == '+' || s[i] == '-')
                    i++;
                if (i >= s.size() || !isdigit(s[i]))
                    return false;
            } else {
                return false;
            }
            i++;
        }
        // Must have at least one digit (reject "." or "+.")
        return has_digit;
    };

    if (isNumeric(x)) {
        throw RuntimeError("Invalid variable name: numeric format is prioritized as literal");
    }
    // TODO: TO identify the invalid variable
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
             static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            //TODO:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {
                Expr body = it->second.first;
                std::vector<std::string> parameters = it->second.second;

                return Value(new Procedure(parameters, body, e));
                //TODO
            }
      }
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    if (rand1->v_type == V_VOID) {
        return IntegerV(0);
    }

    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return IntegerV(p1->n + p2->n);
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->numerator * p2->denominator + p1->denominator * p2->numerator ,
                p1->denominator * p2->denominator);
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->numerator  + p1->denominator * p2->n , p1->denominator );
        }
    }

    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        return Plus::evalRator(rand2, rand1);
    }



    //TODO: To complete the addition logic
    throw(RuntimeError("Wrong typename"));
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    if (auto it = dynamic_cast<Void*>(rand1.get())) {
        if (rand2->v_type == V_INT) {
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            return IntegerV(-(p2->n));
        }else if (rand2->v_type == V_RATIONAL) {
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            return RationalV(-(p2->numerator) , p2->denominator);
        }
    }

    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return IntegerV(p1->n - p2->n);
        }
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
        if (p1 && p2) {
            return RationalV(
                p1->numerator * p2->denominator - p1->denominator * p2->numerator,
                p1->denominator * p2->denominator
            );
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->numerator - p1->denominator * p2->n, p1->denominator);
        }
    }

    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
        const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->n * p2->denominator - p2->numerator, p2->denominator);
        }
    }

    //TODO: To complete the substraction logic
    throw(RuntimeError("Wrong typename"));
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    if (rand1->v_type == V_VOID) {
        return IntegerV(1);
    }

    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return IntegerV(p1->n * p2->n);
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
        if (p1 && p2) {
            return RationalV(
                p1->numerator * p2->numerator,
                p1->denominator * p2->denominator
            );
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->numerator * p2->n, p1->denominator);
        }
    }

    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        return Mult::evalRator(rand2, rand1);
    }
    //TODO: To complete the Multiplication logic
    throw(RuntimeError("Wrong typename"));
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    if (auto it = dynamic_cast<Void*>(rand1.get())) {
        if (rand2->v_type == V_INT) {
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            return RationalV(1,p2->n);
        }else if (rand2->v_type == V_RATIONAL) {
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            return RationalV(p2->denominator , p2->numerator);
        }
    }

    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            if (p2->n == 0) throw(RuntimeError("Division by zero"));
            if (p1->n % p2->n == 0)
                return IntegerV(p1->n / p2->n);
            else
                return RationalV(p1->n, p2->n);
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
        if (p1 && p2) {
            return RationalV( p1->numerator * p2->denominator,
                p1->denominator * p2->numerator );
        }
    }

    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
        const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->numerator, p1->denominator * p2->n);
        }
    }

    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
        const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
        if (p1 && p2) {
            return RationalV(p1->n * p2->denominator, p2->numerator);
        }
    }

    //TODO: To complete the dicision logic
    throw(RuntimeError("Wrong typename"));
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) throw(RuntimeError("+ requires at least one argument"));

    Value result = args[0];

    auto binary_plus = [](const Value& rand1 , const Value& rand2) -> Value {
        if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2) {
                return IntegerV(p1->n + p2->n);
            }
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2) {
                return RationalV(p1->numerator * p2->denominator + p1->denominator * p2->numerator ,
                    p1->denominator * p2->denominator);
            }
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2) {
                return RationalV(p1->numerator  + p1->denominator * p2->n , p1->denominator );
            }
        }

        else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
            const Rational *p1 = dynamic_cast<Rational *>(rand2.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand1.get());
            if (p1 && p2) {
                return RationalV(p1->numerator  + p1->denominator * p2->n , p1->denominator );
            }
        }

        //TODO: To complete the addition logic
        throw(RuntimeError("Wrong typename"));
    };

    for (int i = 1 ; i < args.size() ; ++i) {
        result = binary_plus(result , args[i]);
    }

    return result;

    //TODO: To complete the addition logic
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args

    if (args.empty()) throw(RuntimeError("- requires at least one argument"));

    Value result = args[0];

    auto binary_minus = [](const Value &rand1, const Value &rand2) -> Value {
        if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2) return IntegerV(p1->n - p2->n);
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->numerator * p2->denominator - p1->denominator * p2->numerator,
                                 p1->denominator * p2->denominator);
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->numerator - p1->denominator * p2->n, p1->denominator);
        }

        else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->n * p2->denominator - p2->numerator, p2->denominator);
        }

        throw(RuntimeError("Wrong typename"));
    };

    for (int i = 1; i < args.size(); ++i) {
        result = binary_minus(result, args[i]);
    }

    return result;
    //TODO: To complete the substraction logic
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args

    if (args.empty()) throw(RuntimeError("* requires at least one argument"));

    Value result = args[0];

    auto binary_mult = [](const Value &rand1, const Value &rand2) -> Value {
        if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2) return IntegerV(p1->n * p2->n);
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->numerator * p2->numerator,
                                 p1->denominator * p2->denominator);
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->numerator * p2->n, p1->denominator);
        }

        else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->n * p2->numerator, p2->denominator);
        }

        throw(RuntimeError("Wrong typename"));
    };

    for (int i = 1; i < args.size(); ++i) {
        result = binary_mult(result, args[i]);
    }

    return result;
    //TODO: To complete the multiplication logic
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args

    if (args.empty()) throw(RuntimeError("/ requires at least one argument"));

    Value result = args[0];

    auto binary_div = [](const Value &rand1, const Value &rand2) -> Value {
        if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2) {
                if (p2->n == 0) throw(RuntimeError("Division by zero"));
                if (p1->n % p2->n == 0) return IntegerV(p1->n / p2->n);
                else return RationalV(p1->n, p2->n);
            }
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->numerator * p2->denominator,
                                 p1->denominator * p2->numerator);
        }

        else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
            const Rational *p1 = dynamic_cast<Rational *>(rand1.get());
            const Integer *p2 = dynamic_cast<Integer *>(rand2.get());
            if (p1 && p2) {
                if (p2->n == 0) throw(RuntimeError("Division by zero"));
                return RationalV(p1->numerator, p1->denominator * p2->n);
            }
        }

        else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
            const Integer *p1 = dynamic_cast<Integer *>(rand1.get());
            const Rational *p2 = dynamic_cast<Rational *>(rand2.get());
            if (p1 && p2)
                return RationalV(p1->n * p2->denominator, p2->numerator);
        }

        throw(RuntimeError("Wrong typename"));
    };

    for (int i = 1; i < args.size(); ++i) {
        result = binary_div(result, args[i]);
    }

    return result;
    //TODO: To complete the divisor logic
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
    {
        bool ans = (compareNumericValues(rand1 , rand2) == -1);
        return BooleanV(ans);
    }
    //TODO: To complete the less logic
    throw(RuntimeError("Wrong typename"));
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
    {
        bool ans = (compareNumericValues(rand1 , rand2) != 1);
        return BooleanV(ans);
    }
    //TODO: To complete the lesseq logic
    throw(RuntimeError("Wrong typename"));
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
    {
        bool ans = (compareNumericValues(rand1 , rand2) == 0);
        return BooleanV(ans);
    }
    //TODO: To complete the equal logic
    throw(RuntimeError("Wrong typename"));
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
    {
        bool ans = (compareNumericValues(rand1 , rand2) != -1);
        return BooleanV(ans);
    }
    //TODO: To complete the greatereq logic
    throw(RuntimeError("Wrong typename"));
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
    {
        bool ans = (compareNumericValues(rand1 , rand2) == 1);
        return BooleanV(ans);
    }
    //TODO: To complete the greater logic
    throw(RuntimeError("Wrong typename"));
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    auto cmp = [](const Value &rand1, const Value &rand2)->bool {
        if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) && (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
        {
            bool ans = (compareNumericValues(rand1 , rand2) == -1);
            return ans;
        }
        throw(RuntimeError("Wrong typename"));
    };
    for (int i = 0 ; i < args.size()-1 ; ++i) {
        if (!cmp(args[i] , args[i+1])) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
    //TODO: To complete the less logic
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    auto cmp = [](const Value &rand1, const Value &rand2)->bool {
        if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) &&
            (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
        {
            bool ans = (compareNumericValues(rand1, rand2) != 1);
            return ans;
        }
        throw(RuntimeError("Wrong typename"));
    };
    for (int i = 0; i < args.size() - 1; ++i) {
        if (!cmp(args[i], args[i + 1])) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
    //TODO: To complete the lesseq logic
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    auto cmp = [](const Value &rand1, const Value &rand2)->bool {
        if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) &&
            (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
        {
            bool ans = (compareNumericValues(rand1, rand2) == 0);
            return ans;
        }
        throw(RuntimeError("Wrong typename"));
    };
    for (int i = 0; i < args.size() - 1; ++i) {
        if (!cmp(args[i], args[i + 1])) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
    //TODO: To complete the equal logic
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    auto cmp = [](const Value &rand1, const Value &rand2)->bool {
        if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) &&
            (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
        {
            bool ans = (compareNumericValues(rand1, rand2) != -1);
            return ans;
        }
        throw(RuntimeError("Wrong typename"));
    };
    for (int i = 0; i < args.size() - 1; ++i) {
        if (!cmp(args[i], args[i + 1])) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
    //TODO: To complete the greatereq logic
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    auto cmp = [](const Value &rand1, const Value &rand2)->bool {
        if ((rand1->v_type == V_INT || rand1->v_type == V_RATIONAL) &&
            (rand2->v_type == V_INT || rand2->v_type == V_RATIONAL))
        {
            bool ans = (compareNumericValues(rand1, rand2) == 1);
            return ans;
        }
        throw(RuntimeError("Wrong typename"));
    };
    for (int i = 0; i < args.size() - 1; ++i) {
        if (!cmp(args[i], args[i + 1])) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
    //TODO: To complete the greater logic
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1,rand2);
    //TODO: To complete the cons logic
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    if (args.empty()) return PairV(NullV() , NullV());

    auto list_tail = PairV(args.back() , NullV());

    if (args.size() == 1) return list_tail;
    auto i = args.end()-1;
    do {
        --i;
        list_tail = PairV(*i , list_tail);
    }while ( i != args.begin());

    return list_tail;
    //TODO: To complete the list logic
}

Value IsList::evalRator(const Value &rand) { // list?

    if (rand->v_type == V_PAIR) {

        auto check = dynamic_cast<Pair*>(rand.get());

        if (check->cdr->v_type == V_PAIR) {
            return IsList::evalRator(check->cdr);

        }else if (check->cdr->v_type == V_NULL) {
            return BooleanV(true);

        }else {
            return BooleanV(false);
        }
    }

    return BooleanV(false);
    //TODO: To complete the list? logic
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("Not a pair");
    }
    auto temp = dynamic_cast<Pair*>(rand.get());

    return temp->car;

    //TODO: To complete the car logic
}

Value Cdr::evalRator(const Value &rand) { // cdr

    if (rand->v_type != V_PAIR) {
        throw RuntimeError("Not a pair");

    }
    auto temp = dynamic_cast<Pair*>(rand.get());

    return temp->cdr;
    //TODO: To complete the cdr logic
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    //TODO: To complete the set-car! logic
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
   //TODO: To complete the set-cdr! logic
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // 检查类型是否为 Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // 检查类型是否为 Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // 检查类型是否为 Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // 检查类型是否为 Null 或 Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {
    for (auto it = es.begin() ; it != es.end() ; ++it) {
        if (it == es.end()-1) {
            return (*it) -> eval(e);
        }
        (*it)->eval(e);
    }
    //TODO: To complete the begin logic
}

Value convert(const Syntax& s) {
    if (auto Num = dynamic_cast<Number*>(s.get())) {
        return IntegerV(Num->n);
    }
    if (auto Rat = dynamic_cast<RationalSyntax*>(s.get())) {
        return RationalV(Rat->numerator , Rat->denominator);
    }
    if (auto Sym = dynamic_cast<SymbolSyntax*>(s.get())) {
        return SymbolV(Sym->s);
    }
    if (auto Str = dynamic_cast<StringSyntax*>(s.get())){
        return StringV(Str->s);
    }
    if (auto True = dynamic_cast<TrueSyntax*>(s.get())) {
        return BooleanV(true);
    }
    if (auto False = dynamic_cast<FalseSyntax*>(s.get())) {
        return BooleanV(false);
    }
    if (auto Lst = dynamic_cast<List*>(s.get())) {
        if (Lst->stxs.empty()) {
            return NullV();
        }
        int dot_count = 0;
        int dot_pos = -1;
        auto stxs = Lst->stxs;
        for (size_t i = 0; i < stxs.size(); ++i) {
            if (auto sym = dynamic_cast<SymbolSyntax *>(stxs[i].get())) {
                if (sym->s == ".") {
                    ++dot_count;
                    if (dot_pos < 0) dot_pos = i;
                }
            }
        }

        if (dot_count > 1) {
            throw RuntimeError("Illegal dot num");
        }
        if (dot_count == 0) {
            std::vector<Value> result;
            for (const auto& i : Lst->stxs) {
                result.emplace_back(convert(i));
            }

            auto mk_list = [&](const std::vector<Value> &args) {
                auto list_tail = PairV(args.back() , NullV());

                if (args.size() == 1) return list_tail;
                auto i = args.end() - 1;
                do {
                    --i;
                    list_tail = PairV(*i , list_tail);
                }while ( i != args.begin());

                return list_tail;
            };

            return mk_list(result);
        }
        else {
            std::vector<Value> result;
            for (const auto& i : Lst->stxs) {
                result.emplace_back(convert(i));
            }
            if (stxs.size() < 3 || (dot_pos != stxs.size()-2) || dot_pos == 0) {
                throw RuntimeError("Wrong dot position");
            }else {
                auto ans = PairV(convert(stxs[stxs.size()-3]) , convert(stxs[stxs.size()-1]));
                for (int i = stxs.size()-3 ; i >=0 ; --i) {
                    if (i != stxs.size()-3) {
                        ans=PairV(convert(stxs[i]) , ans);
                    }
                }
                return ans;
            }
        }
    }

    throw RuntimeError("Wrong Type");
}

Value Quote::eval(Assoc& e) {
    return convert(s);
    //TODO: To complete the quote logic
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(true) ;
    }

    Value result = VoidV();

    for (auto &expr : rands) {
        result = expr->eval(e);

        if (auto b = dynamic_cast<Boolean*>(result.get())) {
            if (!b->b) return BooleanV(false); // short circuit
        }
    }

    return result;

    //TODO: To complete the and logic
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(false);
    }
    Value result = VoidV();
    for (const auto& i : rands) {
        result = i->eval(e);
        if (result->v_type != V_BOOL) {
            return result;
        }else {
            if (dynamic_cast<Boolean*>(result.get())->b == true) {
                return BooleanV(true);
            }
        }

    }
    return BooleanV(false);
    //TODO: To complete the or logic
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL) {
        auto pt = dynamic_cast<Boolean*>(rand.get());
        if (pt->b == false) {
            return BooleanV(true);
        }
    }
    return BooleanV(false);
    //TODO: To complete the not logic
}

Value If::eval(Assoc &e) {
    auto condition = cond->eval(e);
    if (condition->v_type == V_BOOL) {
        auto i = dynamic_cast<Boolean*>(condition.get());
        if (i->b == false) {
            return alter->eval(e);
        }
    }
    return conseq->eval(e);
    //TODO: To complete the if logic
}

bool test_conditional(const Expr& cond , Assoc &e) {
    auto condition = cond->eval(e);
    if (condition->v_type == V_BOOL) {
        auto i = dynamic_cast<Boolean*>(condition.get());
        if (i->b == false) {
            return false;
        }
    }
    return true;
}

Value Cond::eval(Assoc &env) {
    // clauses: vector<vector<Expr>>
    // 每个 clause 至少应当有一个元素 (predicate 或 'else')
    for (size_t i = 0; i < clauses.size(); ++i) {
        const auto &clause = clauses[i];
        if (clause.empty()) {
            throw RuntimeError("cond: empty clause");
        }

        bool is_else = false;
        if (auto varPtr = dynamic_cast<Var*>(clause[0].get())) {
            if (varPtr->x == "else") is_else = true;
        }

        if (is_else) {
            // else 必须是最后一个子句（parser 应已保证）；这里再次保护性检查
            if (i != clauses.size() - 1) {
                throw RuntimeError("cond: else clause must be last");
            }
            // 若 else 子句没有后续表达式，返回 Void
            if (clause.size() == 1) return VoidV();

            // 顺序执行 consequents，返回最后一个的值
            Value result = VoidV();
            for (size_t j = 1; j < clause.size(); ++j) {
                result = clause[j]->eval(env);
            }
            return result;
        } else {
            // 普通子句：先计算 predicate（且只计算一次）
            Value test_val = clause[0]->eval(env);

            // 判定 truthiness：只有 #f （V_BOOL 且 false）为假，其它都为真
            bool is_false = (test_val->v_type == V_BOOL) &&
                            (dynamic_cast<Boolean*>(test_val.get())->b == false);

            if (!is_false) {
                // predicate 为真：如果没有后续表达式则返回 predicate 的值
                if (clause.size() == 1) {
                    return test_val;
                }
                // 否则顺序执行 consequents，返回最后一个的值
                Value result = VoidV();
                for (size_t j = 1; j < clause.size(); ++j) {
                    result = clause[j]->eval(env);
                }
                return result;
            }
            // predicate 为假：继续检查下一个 clause
        }
    }

    // 若所有子句都不匹配，返回 Void（你也可以选择返回 VoidV() 或者抛错，根据你原来设计）
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x,e,env);
    //TODO: To complete the lambda logic
}

// Value Apply::eval(Assoc &e) {
//     Value rator_val = rator->eval(e);
//
//     if (rator_val.get() == nullptr || rator_val->v_type != V_PROC) {
//         throw RuntimeError("Attempt to apply a non-procedure");
//     }
//     //TODO: TO COMPLETE THE CLOSURE LOGIC
//     Procedure* clos_ptr = dynamic_cast<Procedure *>(rator_val.get());
//
//     //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
//     std::vector<Value> args;
//     // if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
//     //     args.emplace_back(varNode->eval(e));
//     //     //TODO
//     // }
//     args.reserve(rand.size());
//     for (auto &randExpr : rand) {
//         args.push_back(randExpr->eval(e));
//     }
//     if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");
//
//     //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
//     Assoc param_env = clos_ptr->env;
//     for (size_t i = 0 ; i < args.size() ; ++i) {
//         param_env = extend(clos_ptr->parameters[i] , args[i] , param_env);
//     }
//
//     return clos_ptr->e->eval(param_env);
// }


Value Apply::eval(Assoc &e) {
	Value proc_val = rator->eval(e);
    if (proc_val->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}
    //TODO: TO COMPLETE THE CLOSURE LOGIC
    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());
	 if (!clos_ptr) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }
    //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    std::vector<Value> args;
	for (const auto& arg_expr : rand) {
    	args.push_back(arg_expr->eval(e));
	}
   bool is_variadic = false;
	// 判断是否为可变参数函数
	if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
    	is_variadic = true;  // 标记为可变参数，后续跳过严格的数量检查
	}
    if (!is_variadic&&args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");

    //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    Assoc param_env = clos_ptr->env;
	for (size_t i = 0; i < clos_ptr->parameters.size(); ++i) {
        extend(clos_ptr->parameters[i], args[i] , param_env);  //w 绑定形参和实参
    }
	if (auto* makeVoid = dynamic_cast<MakeVoid*>(clos_ptr->e.get())) {
        return makeVoid->eval(e);  // MakeVoid无参数，直接调用eval
    } else if (auto* exitFunc = dynamic_cast<Exit*>(clos_ptr->e.get())) {
        return exitFunc->eval(e);  // Exit无参数，直接调用eval
    }
    // 2. 单参数内置函数（isboolean、isfixnum、null?、pair?、procedure?、symbol?、string?、display、not、null?、pair?、islist、car、cdr）
    else if (auto* isBoolean = dynamic_cast<IsBoolean*>(clos_ptr->e.get())) {
        return isBoolean->evalRator(args[0]);  // boolean? 接收1个参数
    } else if (auto* isFixnum = dynamic_cast<IsFixnum*>(clos_ptr->e.get())) {
        return isFixnum->evalRator(args[0]);  // isfixnum 接收1个参数
    } else if (auto* isNull = dynamic_cast<IsNull*>(clos_ptr->e.get())) {
        return isNull->evalRator(args[0]);  // null? 接收1个参数
    } else if (auto* isPair = dynamic_cast<IsPair*>(clos_ptr->e.get())) {
        return isPair->evalRator(args[0]);  // pair? 接收1个参数
    } else if (auto* isProcedure = dynamic_cast<IsProcedure*>(clos_ptr->e.get())) {
        return isProcedure->evalRator(args[0]);  // procedure? 接收1个参数
    } else if (auto* isSymbol = dynamic_cast<IsSymbol*>(clos_ptr->e.get())) {
        return isSymbol->evalRator(args[0]);  // symbol? 接收1个参数
    } else if (auto* isString = dynamic_cast<IsString*>(clos_ptr->e.get())) {
        return isString->evalRator(args[0]);  // string? 接收1个参数
    } else if (auto* displayFunc = dynamic_cast<Display*>(clos_ptr->e.get())) {
        return displayFunc->evalRator(args[0]);  // display 接收1个参数
    } else if (auto* notFunc = dynamic_cast<Not*>(clos_ptr->e.get())) {
        return notFunc->evalRator(args[0]);  // not 接收1个参数
    } else if (auto* isList = dynamic_cast<IsList*>(clos_ptr->e.get())) {
        return isList->evalRator(args[0]);  // list? 接收1个参数
    } else if (auto* carFunc = dynamic_cast<Car*>(clos_ptr->e.get())) {
        return carFunc->evalRator(args[0]);  // car 接收1个参数
    } else if (auto* cdrFunc = dynamic_cast<Cdr*>(clos_ptr->e.get())) {
        return cdrFunc->evalRator(args[0]);  // cdr 接收1个参数
    }
    // 3. 双参数内置函数（modulo、expt、eq?、cons、set-car!、set-cdr!）
    else if (auto* moduloFunc = dynamic_cast<Modulo*>(clos_ptr->e.get())) {
        return moduloFunc->evalRator(args[0], args[1]);  // modulo 接收2个参数
    } else if (auto* exptFunc = dynamic_cast<Expt*>(clos_ptr->e.get())) {
        return exptFunc->evalRator(args[0], args[1]);  // expt 接收2个参数
    } else if (auto* isEq = dynamic_cast<IsEq*>(clos_ptr->e.get())) {
        return isEq->evalRator(args[0], args[1]);  // eq? 接收2个参数
    } else if (auto* consFunc = dynamic_cast<Cons*>(clos_ptr->e.get())) {
        return consFunc->evalRator(args[0], args[1]);  // cons 接收2个参数
    } else if (auto* setCar = dynamic_cast<SetCar*>(clos_ptr->e.get())) {
        return setCar->evalRator(args[0], args[1]);  // set-car! 接收2个参数
    } else if (auto* setCdr = dynamic_cast<SetCdr*>(clos_ptr->e.get())) {
        return setCdr->evalRator(args[0], args[1]);  // set-cdr! 接收2个参数
    }
    // 4. 可变参数内置函数（+、-、*、/、=、<、<=、>、>=、list）
    else if (auto* plusVar = dynamic_cast<PlusVar*>(clos_ptr->e.get())) {
        return plusVar->evalRator(args);  // + 接收可变参数（vector<Value>）
    } else if (auto* minusVar = dynamic_cast<MinusVar*>(clos_ptr->e.get())) {
        return minusVar->evalRator(args);  // - 接收可变参数
    } else if (auto* multVar = dynamic_cast<MultVar*>(clos_ptr->e.get())) {
        return multVar->evalRator(args);  // * 接收可变参数
    } else if (auto* divVar = dynamic_cast<DivVar*>(clos_ptr->e.get())) {
        return divVar->evalRator(args);  // / 接收可变参数（注意：你原代码中DivVar::evalRator调用了Dis，需改为Div）
    } else if (auto* equalVar = dynamic_cast<EqualVar*>(clos_ptr->e.get())) {
        return equalVar->evalRator(args);  // = 接收可变参数
    } else if (auto* lessVar = dynamic_cast<LessVar*>(clos_ptr->e.get())) {
        return lessVar->evalRator(args);  // < 接收可变参数
    } else if (auto* lessEqVar = dynamic_cast<LessEqVar*>(clos_ptr->e.get())) {
        return lessEqVar->evalRator(args);  // <= 接收可变参数
    } else if (auto* greaterVar = dynamic_cast<GreaterVar*>(clos_ptr->e.get())) {
        return greaterVar->evalRator(args);  // > 接收可变参数
    } else if (auto* greaterEqVar = dynamic_cast<GreaterEqVar*>(clos_ptr->e.get())) {
        return greaterEqVar->evalRator(args);  // >= 接收可变参数
    } else if (auto* listFunc = dynamic_cast<ListFunc*>(clos_ptr->e.get())) {
        return listFunc->evalRator(args);  // list 接收可变参数
    }
    // -------------------------- 非内置函数：执行用户lambda函数 --------------------------
    else {
        return clos_ptr->e->eval(param_env);
    }
}



Value Define::eval(Assoc &env) {


    if (e.get()->e_type == E_LAMBDA) {
        // 当 parser 已经将 (define (f x y) body) 翻译为
        // Define("f", Lambda({x,y}, body))
        Value val = e->eval(env);

        Value existing = find(var, env);
        if (existing.get() != nullptr) {
            modify(var, val, env);
        } else {
            env = extend(var, val, env);
        }

        return VoidV();
    }

    Value val = e->eval(env);

    Value existing = find(var, env);
    if (existing.get() != nullptr) {
        modify(var, val, env);
    } else {
        env = extend(var, val, env);
    }

    return VoidV();
}


Value Let::eval(Assoc &env) {
    //TODO: To complete the let logic
}

Value Letrec::eval(Assoc &env) {
    //TODO: To complete the letrec logic
}

Value Set::eval(Assoc &env) {
    //TODO: To complete the set logic
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
