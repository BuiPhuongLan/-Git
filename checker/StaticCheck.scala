package mc.checker

/**
 * @author nhphung
 * Ho ten: Bui Phuong Lan
 * MSSV: 1511684
 */

import mc.parser._
import mc.utils._
import java.io.{File, PrintWriter}

//import mc.codegen.Val
import org.antlr.v4.runtime.ANTLRFileStream
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.tree._
import scala.collection.JavaConverters._


case class Symbol(name:String,typ:Type,va:Val)
trait Val
case class FunctionType(input:List[Type],output:Type) extends Type

class StaticChecker(ast:AST) extends BaseVisitor with Utils {

	val global = List(Symbol("getInt",FunctionType(List(),IntType),null),
                    Symbol("putInt",FunctionType(List(IntType),VoidType),null),
                    Symbol("putIntLn",FunctionType(List(IntType),VoidType),null),
                    Symbol("getFloat",FunctionType(List(),FloatType),null),
                    Symbol("putFloat",FunctionType(List(FloatType),VoidType),null),
                    Symbol("putFloatLn",FunctionType(List(FloatType),VoidType),null),
                    Symbol("putBool",FunctionType(List(BoolType),VoidType),null),
                    Symbol("putBoolLn",FunctionType(List(BoolType),VoidType),null),
                    Symbol("putString",FunctionType(List(StringType),VoidType),null),
                    Symbol("putStringLn",FunctionType(List(StringType),VoidType),null),
                    Symbol("putLn",FunctionType(List(),VoidType),null))
       
    def check() = visit(ast,global)

    def getName(x:Decl) = x match {
    	//VarDecl(val variable: Id, val varType: Type) extends Decl
    	case VarDecl(Id(m), _) => m
    	case FuncDecl(Id(m), _, _, _) => m
    }

    def getType(x:Decl):Type = x match {
    	case VarDecl(_, t) => t
    	case FuncDecl(_, p, r, _) => FunctionType(p.map(getType), r)
    }

    def getKind(decl: Decl): Kind = {
        if (decl.isInstanceOf[VarDecl]) Variable else Function
    }

    //Program(val decl: List[Decl])
    override def visitProgram(ast: Program, c: Any): Any = {
    	val glenv = ast.decl.foldLeft(global)((x, y) => 
    		if (lookup (getName(y), x, (m: Symbol) => m.name) == None)
    			Symbol (getName(y), getType(y), null) :: x
    		else throw Redeclared (getKind(y), getName(y))
    	)
    	ast.decl.filter(_.isInstanceOf[FuncDecl]).map(_.accept(this, glenv))
    }

    //FuncDecl(val name: Id, val param: List[VarDecl], val returnType: Type,val body: Stmt) extends Decl
    override def visitFuncDecl (ast: FuncDecl, c: Any): Any = {
    	val params = ast.param.foldLeft(List[Symbol]())((x, y) => 
    		if (lookup (getName(y), x, (m: Symbol) => m.name) == None)
    			Symbol (getName(y), getType(y), null) :: x
    		else throw Redeclared (Parameter, getName(y))
    	)   		
    	val blk = ast.body.asInstanceOf[Block]
    	val local = blk.decl.foldLeft(params)((x, y) => 
    		if (lookup (getName(y), x, (m: Symbol) => m.name) == None)
    			Symbol (getName(y), getType(y), null) :: x
    		else throw Redeclared (getKind(y), getName(y))
    	) 
    	val env = local ++ c.asInstanceOf[List[Symbol]]
    	blk.stmt.map(_.accept(this, List(env, ast.returnType)))
    }

    def typeCheck (lhs: Type, rhs: Type, impli: Boolean): Boolean = (lhs, rhs) match {
        case (IntType, IntType)
            | (FloatType, FloatType) 
            | (FloatType, IntType)
            | (StringType, StringType) 
            | (BoolType, BoolType) 
            => true
        case (ArrayPointerType(t1), ArrayPointerType(t2)) => t1 == t2 && impli
        case (ArrayPointerType(t1), ArrayType(_, t2)) => t1 == t2 && impli
        case (FunctionType(l1, _), FunctionType(l2, null)) => 
            if (l1.length == l2.length && impli) l1.zip(l2).forall(x=>typeCheck(x._1, x._2, true))
            else false
        case (_,_) => false
    }

    override def visitIntLiteral(ast: IntLiteral, c: Any): Any = IntType
  	override def visitFloatLiteral(ast: FloatLiteral, c: Any): Any = FloatType
  	override def visitStringLiteral(ast: StringLiteral, c: Any): Any = StringType
  	override def visitBooleanLiteral(ast: BooleanLiteral, c: Any): Any = BoolType

    //If(val expr: Expr, val thenStmt: Stmt, val elseStmt: Option[Stmt]) extends Stmt 
    override def visitIf (ast: If, c: Any): Any = {
        val exp = ast.expr.accept(this,c)
        if (exp != BoolType) throw TypeMismatchInStatement(ast)
        else {
            ast.thenStmt.accept(this,c)
            if (ast.elseStmt != None) ast.elseStmt.get.accept(this,c)
        }
    } 

    //For(val expr1:Expr,  val expr2: Expr, val expr3: Expr, val loop: Stmt) extends Stmt 
    override def visitFor (ast: For, c: Any): Any = {
        if (ast.expr1.accept(this,c) != IntType || ast.expr2.accept(this,c) != BoolType || ast.expr3.accept(this,c) != IntType)
            throw TypeMismatchInStatement(ast)
        else ast.loop.accept(this,c)
    }

    //Dowhile(val sl:List[Stmt],val exp:Expr) extends Stmt 
    override def visitDowhile (ast: Dowhile, c:Any): Any = {
        val exp = ast.exp.accept(this,c)
        if (exp != BoolType) throw TypeMismatchInStatement(ast)
        else ast.sl.map(_.accept(this,c))
    }

    //BinaryOp(op: String, left: Expr, right: Expr) extends Expr
    override def visitBinaryOp (ast: BinaryOp, c: Any): Type = {
        val ltype = ast.left.accept(this,c).asInstanceOf[Type]
        val rtype = ast.right.accept(this,c).asInstanceOf[Type]
        ast.op match {
        	case "+" | "-" | "*" | "/" 
        		=> if (ltype == IntType && rtype == IntType) IntType
        			else if ((ltype == IntType || ltype == FloatType) && (rtype == FloatType || rtype == IntType))
        				FloatType
        			else throw TypeMismatchInExpression(ast)
        	case "<" | "<=" | ">" | ">="
        		=> if ((ltype == IntType || ltype == FloatType) && (rtype == FloatType || rtype == IntType))
        				BoolType
        			else throw TypeMismatchInExpression(ast) 
        	case "==" | "!="
        		=> if ((ltype == IntType || ltype == BoolType) && (rtype == BoolType || rtype == IntType))
        				BoolType
        			else throw TypeMismatchInExpression(ast)
        	case "=" 
        		=> if (typeCheck (ltype, rtype, false)) ltype 
        			else throw TypeMismatchInExpression(ast)
        	case "&&" | "||"
        		=> if (ltype == BoolType && rtype == BoolType) BoolType
        			else throw TypeMismatchInExpression(ast)
        	case "%"
        		=> if (ltype == IntType && rtype == IntType) IntType
        			else throw TypeMismatchInExpression(ast)
        	case _ => throw TypeMismatchInExpression(ast)
        }
    }

    //UnaryOp(op: String, body: Expr) extends Expr
    override def visitUnaryOp(ast: UnaryOp, c: Any): Type = {
    	val expType = ast.body.accept(this, c).asInstanceOf[Type]
    	ast.op match {
    		case "-" => if (expType == IntType) IntType
    		 			else if (expType == FloatType) FloatType
    		 			else throw TypeMismatchInExpression(ast)
    		case "!" => if (expType == BoolType) BoolType
    					else throw TypeMismatchInExpression(ast)
    		case _ => throw TypeMismatchInExpression(ast)
    	}
    }
   
    //CallExpr(val method: Id, val params: List[Expr]) extends Expr
    override def visitCallExpr (ast: CallExpr, c: Any): Type = {
        //val env = c.asInstanceOf[List[Symbol]]
        val env = c.asInstanceOf[List[Any]](0).asInstanceOf[List[Symbol]]
        val at = ast.params.map(visit(_,c).asInstanceOf[Type])
        val res = lookup(ast.method.name,env,(x:Symbol)=>x.name)
        res match {
            case Some(Symbol(_,FunctionType(pl,rt),_)) =>
                if (pl.length!=at.length || !typeCheck(FunctionType(pl,rt), FunctionType(at, null), true))
                	throw TypeMismatchInExpression(ast)
                else rt
            case Some(_) | None => throw Undeclared(Function,ast.method.name)
        }
    }

    //Id(val name: String) extends LHS
    override def visitId(ast: Id, c: Any): Type = {
        val env = c.asInstanceOf[List[Any]](0).asInstanceOf[List[Symbol]]
        val id = lookup(ast.name, env, (s:Symbol) => s.name)
        if (id == None || id.get.typ.isInstanceOf[FunctionType]) throw Undeclared(Identifier,ast.name)
        else id.get.typ
    }

    //ArrayCell(arr: Expr, idx: Expr) extends LHS
    override def visitArrayCell(ast: ArrayCell, c: Any): Type = {
    	val expType = ast.arr.accept(this, c).asInstanceOf[Type]
    	val idxType = ast.idx.accept(this, c).asInstanceOf[Type]
    	if (idxType != IntType) throw TypeMismatchInExpression(ast)
    	expType match {
    		case ArrayPointerType (t) => t
    		case ArrayType (_, t) => t
    		case _ => throw TypeMismatchInExpression(ast)
    	}   	
    }

    //Block(val decl: List[Decl], val stmt: List[Stmt]) extends Stmt
    override def visitBlock(ast: Block, c: Any): Any = {
        val local = ast.decl.foldLeft(List[Symbol]()) ((x,y) => 
        	if (lookup(getName(y),x,(s:Symbol)=>s.name) == None)
            	Symbol(getName(y), getType(y), null) :: x
            else throw Redeclared(Variable, getName(y)) 
        )
    	val env = local ++ c.asInstanceOf[List[Any]](0).asInstanceOf[List[Symbol]]
    	ast.stmt.map(_.accept(this, List(env, c.asInstanceOf[List[Any]](1))));
    }

    //Return(val expr: Option[Expr]) extends Stmt 
    override def visitReturn(ast: Return, c: Any): Any = {
    	val returnType = c.asInstanceOf[List[Any]](1).asInstanceOf[Type]
        ast.expr match {
            case None => if (returnType != VoidType) throw TypeMismatchInStatement(ast)
            case Some(exp) => if (!typeCheck(returnType, exp.accept(this,c).asInstanceOf[Type] , true)) 
            					throw TypeMismatchInStatement(ast)
        }
    }   
  
}
