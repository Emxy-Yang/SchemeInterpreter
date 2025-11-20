#include "Def.hpp"
#include "syntax.hpp"
#include "expr.hpp"
#include "value.hpp"
#include "RE.hpp"
#include <sstream>
#include <iostream>
#include <map>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

bool isExplicitVoidCall(Expr expr) {
    MakeVoid* make_void_expr = dynamic_cast<MakeVoid*>(expr.get());
    if (make_void_expr != nullptr) {
        return true;
    }

    Apply* apply_expr = dynamic_cast<Apply*>(expr.get());
    if (apply_expr != nullptr) {
        Var* var_expr = dynamic_cast<Var*>(apply_expr->rator.get());
        if (var_expr != nullptr && var_expr->x == "void") {
            return true;
        }
    }

    Begin* begin_expr = dynamic_cast<Begin*>(expr.get());
    if (begin_expr != nullptr && !begin_expr->es.empty()) {
        return isExplicitVoidCall(begin_expr->es.back());
    }

    If* if_expr = dynamic_cast<If*>(expr.get());
    if (if_expr != nullptr) {
        return isExplicitVoidCall(if_expr->conseq) || isExplicitVoidCall(if_expr->alter);
    }

    Cond* cond_expr = dynamic_cast<Cond*>(expr.get());
    if (cond_expr != nullptr) {
        for (const auto& clause : cond_expr->clauses) {
            if (clause.size() > 1 && isExplicitVoidCall(clause.back())) {
                return true;
            }
        }
    }
    return false;
}

void REPL(){
    Assoc global_env = empty();
    while (1){
#ifndef ONLINE_JUDGE
        std::cout << "scm> ";
        std::cout.flush(); // 确保提示符在读取输入前被打印出来
#endif

        // ... read and parse ...
        Syntax stx = readSyntax(std :: cin);

        // 增加一个检查：如果读到了文件流结束(EOF)，直接退出
        // 这样可以防止最后多打印一个 scm>
        if (!std::cin) break;

        try{
            Expr expr = stx -> parse(global_env);
            Value val = expr -> eval(global_env);

            if (val -> v_type == V_TERMINATE)
                break;

            if (val.get()) {
                if (val->v_type != V_VOID_DEFINE) {
                    val->show(std::cout);
                    puts("");
                } else {
                    // 【修改建议】
                    // 如果是 define，虽然不打印值，但为了视觉整洁，
                    // 你可以在这里打印一个换行符，这样下一个 scm> 就会在新的一行。
                    // 如果你不希望有空行，就删掉下面这行，但必须接受 scm> "A" 的现象。
                    // puts("");
                }
            }
        }
        catch (const RuntimeError &RE){
            //std :: cout << RE.message();
            std :: cout << "RuntimeError"; // 你的输出示例里这里没有换行，可能会导致粘连
            puts("");

            // 发生错误后，清理输入流是个好习惯
            if (std::cin.peek() == '\n') std::cin.get();
        }

        // 吃掉残留换行符（正如上一个回答提到的，这对交互体验很重要）
        while (std::cin.peek() == '\n' || std::cin.peek() == ' ' || std::cin.peek() == '\r') {
            std::cin.get();
        }
    }
}


int main(int argc, char *argv[]) {
    REPL();
    return 0;
}
