package mc.astgen
import org.antlr.v4.runtime.Token
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ParserRuleContext
import java.io.{PrintWriter,File}
import org.antlr.v4.runtime.ANTLRFileStream
import mc.utils._
import scala.collection.JavaConverters._
import org.antlr.v4.runtime.tree._
import mc.parser._
import mc.parser.MCParser._

class ASTGeneration extends MCBaseVisitor[Any] {
    
    def higReverse(a:List[AST]):List[AST] = a.foldLeft(List[AST]())((x,y) => y::x)
    def higAppend(a:List[AST],b:List[AST]) = higReverse(a).foldLeft(b)((x,y) => y::x)

// program : declaration+ EOF;
    override def visitProgram(ctx: ProgramContext) =
        Program(ctx.declaration.asScala.toList.foldLeft(List[Decl]())((a,b) => higAppend(
            a, b.accept(this).asInstanceOf[List[Decl]]).asInstanceOf[List[Decl]]))
	
// declaration : varDeclaration | funDeclaration ;
	override def visitDeclaration (ctx: DeclarationContext) =
        if (ctx.varDeclaration != null)
            ctx.varDeclaration.accept(this)
        else
            List(ctx.funDeclaration.accept(this))

//  VarDecl(val variable: Id, val varType: Type)
//  varDeclaration : primit idlist (COMMA idlist)* SEMI ;

    override def visitVarDeclaration (ctx: VarDeclarationContext) =
        ctx.idlist.asScala.toList.map(x => 
            if (x.getChildCount() == 1) 
                VarDecl(x.accept(this).asInstanceOf[Id], ctx.primit().accept(this).asInstanceOf[Type])
            else 
                VarDecl(x.accept(this).asInstanceOf[Id], ArrayType(IntLiteral(x.INTLIT.getText.toInt) ,
                    ctx.primit().accept(this).asInstanceOf[Type]))
        )
//  idlist : ID | ID LSB INTLIT RSB;
    override def visitIdlist (ctx: IdlistContext) =
        Id(ctx.ID.getText)

//primit : BOOLEANTYPE | INTTYPE | FLOATTYPE | STRINGTYPE;
    override def visitPrimit(ctx: PrimitContext) =
        if (ctx.INTTYPE != null)
            IntType
        else if (ctx.FLOATTYPE != null)
            FloatType
        else if (ctx.BOOLEANTYPE != null)
            BoolType
        else
            StringType

// funDeclaration : alltype ID LB paralist RB blockstmt ;
    override def visitFunDeclaration (ctx: FunDeclarationContext) =
        FuncDecl (Id(ctx.ID.getText),
            ctx.paralist.accept(this).asInstanceOf[List[VarDecl]],
            ctx.alltype.accept(this).asInstanceOf[Type],
            ctx.blockstmt.accept(this).asInstanceOf[Stmt]
        )

//paralist: (par (COMMA par)*)?;
    override def visitParalist(ctx: ParalistContext) =
        if (ctx.getChildCount != 0)
            ctx.par.asScala.toList.map(_.accept(this))
        else
            List[VarDecl]()

// par : primit ID | primit ID LSB RSB ;
    override def visitPar (ctx: ParContext) =
        if (ctx.getChildCount == 2)
            VarDecl(Id(ctx.ID.getText), ctx.primit.accept(this).asInstanceOf[Type])
        else
            VarDecl(Id(ctx.ID.getText), ArrayPointerType(ctx.primit.accept(this).asInstanceOf[Type]))

//Block(val decl: List[Decl], val stmt: List[Stmt])
// blockstmt : LP varDeclaration* stmt* RP ;
    override def visitBlockstmt (ctx: BlockstmtContext) =
        Block(ctx.varDeclaration.asScala.toList.foldLeft(List[VarDecl]())((a,b) => higAppend(a, b.accept(this).asInstanceOf[List[VarDecl]]).asInstanceOf[List[VarDecl]]), 
            ctx.stmt.asScala.toList.map(_.accept(this).asInstanceOf[Stmt]))

// stmt: matchState | unmatchState;
    override def visitStmt (ctx: StmtContext) =
        ctx.getChild(0).accept(this)

// matchState : IF LB expr RB matchState ELSE matchState | otherState;
    override def visitMatchState (ctx: MatchStateContext) =
        if (ctx.getChildCount == 7)
            If(ctx.expr.accept(this).asInstanceOf[Expr], 
            ctx.matchState(0).accept(this).asInstanceOf[Stmt], 
            Some(ctx.matchState(1).accept(this).asInstanceOf[Stmt]))
        else ctx.otherState.accept(this)

// unmatchState: IF LB expr RB matchState ELSE unmatchState | IF LB expr RB stmt ; 
    override def visitUnmatchState (ctx: UnmatchStateContext) =
        if (ctx.getChildCount() == 7) If(ctx.expr.accept(this).asInstanceOf[Expr], 
            ctx.matchState().accept(this).asInstanceOf[Stmt], 
            Some(ctx.unmatchState().accept(this).asInstanceOf[Stmt]))
        else If(ctx.expr.accept(this).asInstanceOf[Expr], 
            ctx.stmt().accept(this).asInstanceOf[Stmt],None)

//otherState : dowhile_state | for_state | brk_state | conti_state | return_state | expr SEMI | blockstmt;
    override def visitOtherState (ctx: OtherStateContext) =
        if (ctx.getChildCount == 2)
            ctx.expr.accept(this)
        else
            ctx.getChild(0).accept(this)

// dowhile_state : DO stmt+ WHILE expr SEMI ; // Dowhile(val sl:List[Stmt],val exp:Expr)
    override def visitDowhile_state (ctx:Dowhile_stateContext) = 
        Dowhile(ctx.stmt.asScala.toList.map(_.accept(this).asInstanceOf[Stmt]),ctx.expr().accept(this).asInstanceOf[Expr])

// for_state : FOR LB expr SEMI expr SEMI expr +RB stmt;
    override def visitFor_state(ctx: For_stateContext) =
        For (ctx.expr(0).accept(this).asInstanceOf[Expr],
            ctx.expr(1).accept(this).asInstanceOf[Expr],
            ctx.expr(2).accept(this).asInstanceOf[Expr],
            ctx.stmt.accept(this).asInstanceOf[Stmt]
        )

// brk_state : BREAK SEMI;
    override def visitBrk_state(ctx: Brk_stateContext) = Break

// conti_state : CONTINUE SEMI;
    override def visitConti_state(ctx: Conti_stateContext) = Continue

// return_state: RETURN SEMI  | RETURN expr SEMI ;
    override def visitReturn_state(ctx: Return_stateContext) = 
        if (ctx.getChildCount() == 2)
            Return(None)
        else Return(Some(ctx.expr.accept(this).asInstanceOf[Expr]))

// funcall : ID LB exprlist RB;
    override def visitFuncall (ctx: FuncallContext) =
        CallExpr (Id(ctx.ID.getText), ctx.exprlist.accept(this).asInstanceOf[List[Expr]])

// exprlist : (expr (COMMA expr)*)? ;
    override def visitExprlist(ctx: ExprlistContext) =
    if (ctx.getChildCount != 0)
      ctx.expr.asScala.toList.map(_.accept(this))
    else
      List[Expr]()

// expr : term ASSIGN expr | term ;
    override def visitExpr (ctx:ExprContext) =
        if (ctx.getChildCount() == 1) 
            ctx.term().accept(this)
        else 
            BinaryOp(ctx.ASSIGN.getText, 
            ctx.term().accept(this).asInstanceOf[Expr], 
            ctx.expr().accept(this).asInstanceOf[Expr])


// term : term OR term_a | term_a;
    override def visitTerm (ctx:TermContext) =
        if (ctx.getChildCount() == 1) 
            ctx.term_a().accept(this)
        else 
            BinaryOp(ctx.OR.getText, ctx.term().accept(this).asInstanceOf[Expr], ctx.term_a().accept(this).asInstanceOf[Expr])


// term_a : term_a AND term_b | term_b ;
    override def visitTerm_a (ctx:Term_aContext) =
        if (ctx.getChildCount() == 1) 
            ctx.term_b().accept(this)
        else 
            BinaryOp (ctx.AND.getText, ctx.term_a().accept(this).asInstanceOf[Expr], ctx.term_b().accept(this).asInstanceOf[Expr])

// term_b : term_c EQUAL term_c | term_c NOTEQ term_c | term_c;
    override def visitTerm_b (ctx: Term_bContext) =
        if (ctx.getChildCount() == 1) 
            ctx.getChild(0).accept(this)
        else BinaryOp (ctx.getChild(1).getText, 
            ctx.term_c(0).accept(this).asInstanceOf[Expr],
            ctx.term_c(1).accept(this).asInstanceOf[Expr]
        )

// term_c : term_d LTHEN term_d | term_d LTEQUAL term_d | term_d GTHEN term_d | term_d GTEQUAL term_d | term_d;
    override def visitTerm_c (ctx: Term_cContext) =
        if (ctx.getChildCount() == 1) 
            ctx.getChild(0).accept(this)
        else BinaryOp (ctx.getChild(1).getText, 
            ctx.term_d(0).accept(this).asInstanceOf[Expr],
            ctx.term_d(1).accept(this).asInstanceOf[Expr]
        )

// term_d : term_d SUB subterma | term_d ADD subterma| subterma;
    override def visitTerm_d (ctx: Term_dContext) =
        if (ctx.getChildCount() == 1) 
            ctx.getChild(0).accept(this)
        else BinaryOp (ctx.getChild(1).getText, 
            ctx.term_d.accept(this).asInstanceOf[Expr],
            ctx.subterma.accept(this).asInstanceOf[Expr]
        )

// subterma : subterma MUL subtermb | subterma DIV subtermb | subterma MOD subtermb| subtermb;
    override def visitSubterma (ctx: SubtermaContext) =
        if (ctx.getChildCount() == 1) 
            ctx.getChild(0).accept(this)
        else BinaryOp (ctx.getChild(1).getText, 
            ctx.subterma.accept(this).asInstanceOf[Expr],
            ctx.subtermb.accept(this).asInstanceOf[Expr]
        )

// subtermb : SUB subtermb | NOT subtermb | subtermc;
    override def visitSubtermb (ctx: SubtermbContext) =
        if (ctx.getChildCount() == 1) 
            ctx.getChild(0).accept(this)
        else UnaryOp(ctx.getChild(0).getText, ctx.subtermb().accept(this).asInstanceOf[Expr])

// subtermc : factor LSB expr RSB | factor;
    override def visitSubtermc (ctx:SubtermcContext) = 
	   if (ctx.getChildCount == 1)
            ctx.getChild(0).accept(this) 
        else ArrayCell (ctx.factor.accept(this).asInstanceOf[Expr],
        ctx.expr.accept(this).asInstanceOf[Expr])

// factor : INTLIT | FLOATLIT | ID | BOOLEANLIT | funcall | STRINGLIT | LB expr RB;
    override def visitFactor (ctx:FactorContext) =
        if(ctx.getChildCount() == 3)    
            ctx.expr().accept(this)
        else if (ctx.INTLIT != null)    
            IntLiteral(ctx.INTLIT.getText.toInt)
        else if (ctx.FLOATLIT != null)         
            FloatLiteral(ctx.FLOATLIT.getText.toFloat)
        else if (ctx.ID != null)        
            Id(ctx.ID.getText)
        else if (ctx.BOOLEANLIT != null)        
            BooleanLiteral(ctx.BOOLEANLIT.getText.toBoolean)
        else if (ctx.STRINGLIT != null)         
            StringLiteral(ctx.STRINGLIT.getText)
        else ctx.funcall.accept(this)

// alltype: VOIDTYPE | primit LSB RSB | primit; ArrayPointerType(val eleType:Type)
    override def visitAlltype (ctx: AlltypeContext) =
        if (ctx.getChildCount == 3)
            ArrayPointerType(ctx.primit.accept(this).asInstanceOf[Type])
        else if (ctx.VOIDTYPE != null)
            VoidType
        else ctx.primit.accept(this)
       
}


	
      
        
