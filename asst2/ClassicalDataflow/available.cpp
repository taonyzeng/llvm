// 15-745 S15 Assignment 2: available.cpp
// Group: jarulraj, nkshah
////////////////////////////////////////////////////////////////////////////////

#include "dataflow.h"

using namespace llvm;

namespace {
    class AvailableExpressions : public FunctionPass {

    public:
        static char ID;

        AvailableExpressions() : FunctionPass(ID)
        {
            // Setup the pass
            Direction direction = Direction::FORWARD;
            MeetOp meet_op = MeetOp::INTERSECTION;

            pass = AEAnalysis(direction, meet_op);
        }

    private:

        // AE Analysis class
        class AEAnalysis : public DataFlow {
        public:

            AEAnalysis() : DataFlow(Direction::INVALID_DIRECTION, MeetOp::INVALID_MEETOP) {	}
            AEAnalysis(Direction direction, MeetOp meet_op) : DataFlow(direction, meet_op) { }

        protected:

            TransferOutput transferFn(BitVector input, std::vector<void*> domain, std::map<void*, int> domainToIndex, BasicBlock* block)
            {
                TransferOutput transferOutput;

                // Calculating the set of expressions generated and killed in BB
                int domainSize = domainToIndex.size();
                BitVector GenSet(domainSize);
                BitVector KillSet(domainSize);

                for(Instruction& II : *block){
                //Instruction* I  = &II;
                //for (BasicBlock::iterator i = block->begin(), e = block->end(); i!=e; ++i) {
                    Instruction * I = &II;
                    // We only care about available expressions for BinaryOperators
                    if (BinaryOperator * BI = dyn_cast<BinaryOperator>(I)) {
                        // Create a new Expression to capture the RHS of the BinaryOperator
                        Expression *expr = new Expression(BI);
                        Expression *match = NULL;
                        bool found = false;

                        for(void* element : domain)
                        {
                            if((*expr) == *((Expression *) element))
                            {
                                found = true;
                                match = (Expression *) element;
                                break;
                            }
                        }

                        // Generated expression
                        if(found)
                        {
                            int valInd = domainToIndex[(void*)match];

                            // The instruction definitely evaluates the expression in RHS here
                            // The expression  will be killed if one of its operands is
                            // redefined subsequently in the BB.
                            GenSet.set(valInd);
                        }
                    }

                    // Killed expressions

                    // The assignment kills all expressions in which the LHS is an operand.
                    // They will be generated if subsequently recomputed in BB.
                    StringRef insn  =  I->getName();
                    if(!insn.empty())
                    {
                        //DBG(outs() << "Insn : " << insn  << "\n");
                        for(auto domain_itr = domain.begin() ; domain_itr != domain.end() ; domain_itr++)
                        {
                            Expression* expr = (Expression*) (*domain_itr);

                            StringRef op1 = expr->v1->getName();
                            StringRef op2 = expr->v2->getName();

                            if(op1.equals(insn) || op2.equals(insn))
                            {
                                //DBG(outs() << "Expr : " << expr->toString()  << " ");
                                // Kill if either operand 1 or 2 match the variable assigned
                                std::map<void*, int>::iterator iter = domainToIndex.find((void*) expr);

                                if (iter != domainToIndex.end())
                                {
                                    //DBG(outs() << "Index : " << (*iter).second  << "\n");
                                    KillSet.set((*iter).second);
                                    GenSet.reset((*iter).second);
                                }
                            }
                        }
                    }

                }


                //update the genSet and killSet for each block.
                if(genSet.find(block) == genSet.end()){
                    genSet[block] = GenSet;
                }

                if(killSet.find(block) == killSet.end()){
                    killSet[block] = KillSet;
                }

                //printBitVector(GenSet);
                //printBitVector(KillSet);
                // Transfer function = GenSet U (input - KillSet)

                transferOutput.element = KillSet;
                // Complement of KillSet
                transferOutput.element.flip();
                // input - KillSet = input INTERSECTION Complement of KillSet
                transferOutput.element &= input;
                transferOutput.element |= GenSet;

                return transferOutput;
            }

        };

        // The pass
        AEAnalysis pass;

        virtual bool runOnFunction(Function &F) {
            // Print Information
            // auto function_name = F.getName();
            DBG(outs() << "FUNCTION :: " << F.getName()  << "\n");
            DataFlowResult output;

            // Setup the pass
            std::vector<void*> domain;
            // Compute the domain

            for(BasicBlock& B : F){
                for(Instruction& I : B){

                    // We only care about available expressions for BinaryOperators
                    if (BinaryOperator * BI = dyn_cast<BinaryOperator>(&I)) {

                        // Create a new Expression to capture the RHS of the BinaryOperator
                        Expression *expr = new Expression(BI);
                        bool found = false;

                        for(void* element : domain)
                        {
                            if((*expr) == *((Expression *) element))
                            {
                                found = true;
                                break;
                            }
                        }

                        if(found == false)
                            domain.push_back(expr);
                        else
                            delete expr;
                    }
                }
            }

            DBG(outs() << "------------------------------------------\n\n");
            DBG(outs() << "DOMAIN :: " << domain.size() << "\n");
            for(void* element : domain){
                DBG(outs() << "Element : " << ((Expression*) element)->toString() << "\n");
            }

            DBG(outs() << "------------------------------------------\n\n");

            // For AEA, the boundary condition is phi and init condition is U.
            BitVector boundaryCond(domain.size(), false);
            BitVector initCond(domain.size(), true);

            // Apply pass
            output = pass.run(F, domain, boundaryCond, initCond);
            //printResult(output);

            // PRINTING RESULTS

            // Map domain values to index in bitvector
            std::map<void*, int> domainToIndex;
            for (int i = 0; i < domain.size(); i++)
                domainToIndex[(void*)domain[i]] = i;

            // We use the results to compute the available expressions
            std::stringstream ss;

            for(BasicBlock& BL : F){
                BasicBlock* block = &BL;

                outs() << "BB Name: "<< block->getName() << "\n";
                outs() << "IN: " << printSet(domain, output.result[block].in, 1) << "\n";
                outs() << "OUT: "<< printSet(domain, output.result[block].out, 1) << "\n";
                outs() << "Gen: "<< printSet(domain, pass.genSet[block], 1) << "\n";
                outs() << "Kill: "<< printSet(domain, pass.killSet[block], 1) << "\n\n";

            }

            // No modification
            return false;
        }

        virtual bool runOnModule(Module& M) {
            bool modified = false;

            // Run analysis on each function
            for (Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI) {
                bool function_modified = false;

                function_modified = runOnFunction(*MI);

                modified |= function_modified;
            }

            return modified;
        }

    };

    char AvailableExpressions::ID = 0;
    RegisterPass<AvailableExpressions> X("available",
                                         "15745 Available Expressions");
}
