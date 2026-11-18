/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2025
   
   Assignment 2, exercise 4
   
  ---------------------------------------------------------------------------

   You need to equip Minesweeper class with a PROPERTY-BASED specification.
   Recall that these specifications are EXCLUSIVELY written in terms 
   of the observers of the class. Hence, the method contracts (requires
   and ensures clauses) cannot use ANY fields of the class!

   The specification must be strong enough to allow: 
   1) the verification of the constructor and all the methods of the class
   2) the verification of the non-failing test cases provided at the end of
      the file and raising of verification errors for the failing ones
   3) the verification of the Main method that demonstrates the use of the class

   Note that:
   * You are NOT allowed to change the code of the class, except for adding
     the required specifications (class invariant, method contracts, etc).
   * You are NOT allowed to add any new methods or fields to the class.
   * You are NOT allowed to change the test cases or the Main method.
   * You are allowed to add helper lemmas if you need them for the verification.

  --------------------------------------------------------------------------
  --------------------------------------------------------------------------
  Hints:

   * Start by writing the class invariant that captures the basic representation
     invariants of the class and add the appropriate method contracts so that
     Dafny verifies the constructor and methods of the class as well as the Main method.
    (you can just comment out the test cases for now to focus on the class and Main method)
    
    * Once the code of the class and the Main method verifies you can try to run it!
      Two different definitions of function GetMineLocations are provided. To run the Main,
      use the one with a body. For verification purposes, either one should work.

    * Finally, add the method contracts to verify the provided non-failing test cases.

  ---------------------------------------------------------------------------

   Instructor: Antonia Lopes
   Student: Pedro Rosa 60294
*/

/********************************************************************************* 
* Data types used in the Minesweeper class
*   One to represent positions of the minesweeper board and
*   Another to represent the game state.
**********************************************************************************/

datatype Position = Position(row: nat, col: nat)
datatype GameState = WON | LOST | ONGOING

/***********************************************************************************
* Function GetMineLocations: returns a set of mine locations for a board of
* given width and height and with a given number of mines.
* 
* Two different definitions are provided:
* 1) An axiomatic one for verification purposes
* 2) A constructive one for running purposes
**********************************************************************************/


// Axiomatic definition of function GetMineLocations for verification purposes
// function GetMineLocations(w: nat, h: nat, m: nat): set<Position>
//   requires w > 1 && h > 1
//   requires 0 < m < w * h
//   ensures {:axiom} |GetMineLocations(w,h,m)| == m
//   ensures {:axiom} forall e :: e in GetMineLocations(w,h,m) ==> 1 <= e.row <= h && 1 <= e.col <= w
//   ensures {:axiom} exists i,j :: 1 <= i <= h && 1 <= j <= w && Position(i,j) !in GetMineLocations(w,h,m)



// Constructive definition of a function GetMineLocations for running purposes
// that places mines in the first m positions of the board (row-wise)
function GetMineLocations(w: nat, h: nat, m: nat): set<Position>
  requires w > 1 && h > 1
  requires 0 < m < w * h
  ensures forall e :: e in GetMineLocations(w,h,m) ==> 1 <= e.row <= h && 1 <= e.col <= w
  ensures |GetMineLocations(w,h,m)| == m
  ensures exists i,j :: 1 <= i <= h && 1 <= j <= w && Position(i,j) !in GetMineLocations(w,h,m)
{
  GetMineLocationsProperties(w, h, m);
  set i,j | 1 <= i <= h && 1 <= j <= w && (i - 1) * w + j <= m :: Position(i,j) 
}

// A lemma to help prove the relevant properties of this GetMineLocations
lemma GetMineLocationsProperties(w: nat, h: nat, m: nat)
  requires w > 1 && h > 1
  requires 0 < m < w * h
  ensures |set i,j | 1 <= i <= h && 1 <= j <= w && (i - 1) * w + j <= m :: Position(i,j)| == m
  ensures exists i,j :: 1 <= i <= h && 1 <= j <= w 
              && Position(i,j) !in (set i,j | 1 <= i <= h && 1 <= j <= w && (i - 1) * w + j <= m :: Position(i,j))
{
// The proof of this lemma would require to much effort and is not the focus of the assignment,
// so we just assume the required properties as axioms.
 assume {:axiom} |set i,j | 1 <= i <= h && 1 <= j <= w && (i - 1) * w + j <= m :: Position(i,j)| == m;
 assume {:axiom} exists i,j :: (1 <= i <= h && 1 <= j <= w
              && Position(i,j) !in (set i,j | 1 <= i <= h && 1 <= j <= w && (i - 1) * w + j <= m :: Position(i,j)));
}


/********************************************************************************* 
* The class Minesweeper 
*  Implements the Minesweeper game logic
**********************************************************************************/

class Minesweeper {
    // Repr
    ghost var Repr : set<object>

  // Number of rows.
  /* private */ const height : nat
  // Number of columns.
  /* private */ const width : nat
  // The number of mines.
  /* private */ const numMines : nat
  // The playing field with mines.
  /* private */ const field : array2<bool>
  // The revealed positions.
  /* private */ const revealed : array2<bool>
  // The flagged positions.
  /* private */ const flagged : array2<bool>
  // Whether the game is still ongoing or the player has won or lost.
  /* private */ var state : GameState


  // The class invariant
  ghost predicate Valid()
    reads this, Repr 
  {
    this in Repr && this.revealed in Repr && this.flagged in Repr && this.field in Repr 
    //COMPLETE ME 
    && height > 1 && width > 1
    && 0 < numMines < height * width
    && field.Length0 == height && field.Length1 == width
    && revealed.Length0 == height && revealed.Length1 == width
    && flagged.Length0 == height && flagged.Length1 == width
    && (state == WON || state == LOST || state == ONGOING)
  }

  /** The observers of Minesweeper objects **/

  // Number of columns of the board
  function Columns(): nat
    reads Repr
    requires Valid()
  {
    this.width
  }

  // Number of lines of the board
  function Lines(): nat
    reads Repr
    requires Valid()
  {
    this.height
  }
  // Whether the game is still ongoing or the player has won orlost
  predicate IsAlive()
    reads Repr
    requires Valid()
  {
    this.state == ONGOING || this.state == WON
  }

  // Whether the player has won the game
  predicate Won()
    reads Repr
    requires Valid()
  {
    this.state == WON
  }

  // Number of mines on the field
  function NumberOfMines(): nat
    reads Repr
    requires Valid()
  {
    numMines
  }

  // Whether the arguments represent a position of the board
  predicate IsPosition(row: nat, col: nat)
    reads this
  {
    1 <= row <= height && 1 <= col <= width
  }

  // Whether the position of the board is open
  predicate IsOpen(row: nat, col: nat)
    reads Repr
    requires Valid()
    requires IsPosition(row, col)
  {
    revealed[row-1,col-1]
  }

  // Whether a closed position of the board is flagged
  predicate IsFlagged(row: nat, col: nat)
    reads Repr
    requires Valid()
    requires IsPosition(row, col)
  {
    flagged[row-1,col-1]
  }

  // Whether a position of the board has a mine 
  // It is only valid to call this predicate 
  // if the position is open or the game is won
  predicate HasMine(row: nat, col: nat)
    reads Repr
    requires Valid()
    requires IsPosition(row, col)    
  {
    field[row-1,col-1]
  }

  // Whether there exists a position of the board without a mine
  // that is still not opened 
  predicate ExistsPositionToOpen()
    reads Repr
    requires Valid()
     
  
  {
    exists i,j :: 0 <= i < height && 0 <= j < width && !field[i,j] && !revealed[i,j]
    
  }

  // The rank of an open position of the board 
  // (number of mines in the neighbouring positions)
  method GetRank(row: nat, col: nat) returns (cnt: nat)
    requires Valid()
    requires IsPosition(row, col)
    requires IsOpen(row,col) || Won()
    ensures Valid()
    ensures IsPosition(row, col)
    ensures IsOpen(row,col) || Won()
    //ensures cnt >= 0

    ensures 0 <= cnt <= 9
  {
    cnt := 0;
    // count neighbouring bombs (0-based indices around (r,c))
    var r, c := row - 1, col - 1;
    var imin := if r == 0 then 0 else r - 1;
    var imax := if r + 1 < height then r + 1 else r;
    var jmin := if c == 0 then 0 else c - 1;
    var jmax := if c + 1 < width then c + 1 else c;
    for i := imin to imax + 1
      invariant cnt <= 3 * (i - imin)
    {
      for j := jmin to jmax + 1
        invariant cnt <= 3 * (i - imin) + (j - jmin)
      {
        if (i != r || j != c) && field[i,j] {
          cnt := cnt + 1;
        }
      }
    }
  }

  /** The constructor of a Minesweeper object **/

  constructor(w: nat, h: nat, m: nat)
    requires w > 1 && h > 1
    requires 0 < m < w * h
    ensures fresh(Repr)
    ensures Valid()
    ensures Columns() == w
    ensures Lines() == h
    ensures NumberOfMines() == m
    ensures ExistsPositionToOpen()
    ensures IsAlive()
    ensures !Won()
    ensures forall row, col :: 1 <= row <= h && 1 <= col <= w ==> !IsOpen(row, col)
    ensures forall row, col :: 1 <= row <= h && 1 <= col <= w ==> !IsFlagged(row, col)
    ensures forall row, col :: 1 <= row <= h && 1 <= col <= w 
                             ==> (HasMine(row, col) <==> Position(row, col) in GetMineLocations(w,h,m))
    //ensures ExistsPositionToOpen()
  {
    height := h;
    width := w;
    numMines := m;
    // create arrays
    field := new bool[h,w];
    revealed := new bool[h,w];
    flagged := new bool[h,w];
    state := ONGOING;
    Repr := {this, flagged, revealed, field};
    new;

    // place mines using the provided function GetMineLocations
    forall i,j | 0 <= i < height && 0 <= j < width {
      field[i,j] := Position(i+1,j+1) in GetMineLocations(width,height,m);
    }

    forall i,j | 0 <= i < height && 0 <= j < width {
      revealed[i,j] := false;
    }

    forall i,j | 0 <= i < height && 0 <= j < width {
      flagged[i,j] := false;
    }

    //Since a property-driven spec does not allow us to 
    //refer to the field directly in the ensures clauses
    //and the predicate HasMine requires the position to be open
    //or the game to be won, we cannot express in the contract
    //that indeed  m mines were placed in the field.
    //Hence, we add here some ghost code to be sure this is
    //indeed the case.
    ghost var minePositions : set<Position> := (set i,j | 1 <= i <= height && 1 <= j <= width && field[i-1,j-1] :: Position(i,j));
    assert minePositions == (set e:Position | e in GetMineLocations(width,height,m));
    assert minePositions == GetMineLocations(width,height,m);
    assert |minePositions| == m;
  }

  /** The modifiers of an object Minesweeper **/

  //Open a position of the board that is not open yet
  //and update the game state accordingly
  //Can be called only if the game is not over
  method Open(row: nat, col: nat)
    modifies Repr
    requires Valid()
    requires IsPosition(row, col)
    requires !IsOpen(row, col)
    requires IsAlive()
    ensures Valid() && fresh(Repr - old(Repr))
    ensures HasMine(row, col) ==> !IsAlive() && !Won()
    ensures IsOpen(row, col)
    ensures !IsAlive() ==> HasMine(row, col)
    ensures forall r,c :: IsPosition(r,c) && !(r == row && c == col) ==> IsOpen(r,c) == old(IsOpen(r,c))
    ensures !IsAlive() ==> !IsAlive() && !Won()
    ensures old(Repr) == Repr
    ensures forall r, c :: IsPosition(r, c) && !(r == row && c == col)
                     ==> IsFlagged(r, c) == old(IsFlagged(r, c))
    ensures HasMine(row, col) ==> !IsAlive() && !Won()
    //ensures (!HasMine(row, col) && IsAlive() && !Won()) ==> ExistsPositionToOpen()
    ensures forall r,c :: IsPosition(r,c) && !(r == row && c == col)
                     ==> IsOpen(r,c) == old(IsOpen(r,c))
    //ensures IsAlive() ==> (!Won() ==> ExistsPositionToOpen())
    //ensures Won() ==> !IsAlive()
    //ensures !IsAlive() ==> !IsAlive() && !Won()
    
    ensures IsAlive() ==> (!Won() ==> ExistsPositionToOpen())
    ensures Won() ==> !ExistsPositionToOpen()
  {
    var r,c := row-1, col-1;
    revealed[r,c] := true;
    if field[r,c] {
      state := LOST;
    }
    else {
      // check if won: every position without a mine must be open
      var allRevealed := true;
      // ghost witness of a closed position without a mine (when !allRevealed)
      ghost var wi: int, wj: int := 0, 0;
      var i := 0;
      while i < height && allRevealed
        invariant 0 <= i <= height
        invariant allRevealed ==>
          forall ii, jj :: 0 <= ii < i && 0 <= jj < width ==> field[ii,jj] || revealed[ii,jj]
        invariant !allRevealed ==>
          0 <= wi < height && 0 <= wj < width && !field[wi,wj] && !revealed[wi,wj]
      {
        var j := 0;
        while j < width && allRevealed
          invariant 0 <= j <= width
          invariant allRevealed ==>
            forall ii, jj :: 0 <= ii < i && 0 <= jj < width ==> field[ii,jj] || revealed[ii,jj]
          invariant allRevealed ==>
            forall jj :: 0 <= jj < j ==> field[i,jj] || revealed[i,jj]
          invariant !allRevealed ==>
            0 <= wi < height && 0 <= wj < width && !field[wi,wj] && !revealed[wi,wj]
        {
          if !field[i,j] && !revealed[i,j] {
            allRevealed := false;
            wi, wj := i, j;
          }
          j := j + 1;
        }
        i := i + 1;
      }
      state := if allRevealed then WON else ONGOING;
    }
  }

  //Toggle the flagged status of a closed position of the board
  //Can be called only if the game is not over
  method ToggleFlag(row: nat, col: nat)
    modifies Repr
    requires Valid()
    requires IsPosition(row, col)
    requires !IsOpen(row, col)
    requires IsAlive()
    ensures Valid() && fresh(Repr - old(Repr))
    ensures IsFlagged(row, col) <==> !old(IsFlagged(row, col))
    ensures old(Repr) == Repr
    ensures forall r, c :: IsPosition(r, c) && !(r == row && c == col)
                     ==> IsFlagged(r, c) == old(IsFlagged(r, c))

  {
    var r,c := row-1, col-1;
    flagged[r,c] := !flagged[r,c];
  }

  // Returns a string representation of the board, showing
  // opened positions with their rank, flagged positions with '?'
  // and closed positions with ' '. If the game is over (won or lost),
  // the bombs are shown with '*'.
  method BoardToString() returns (s: string)
  requires Valid()
  ensures Valid()
  {
    s := "";
    var showBombs := (state != ONGOING); // show bombs when finished
    for i := 0 to height  {
      for j := 0 to width {
        var aux := " ";
        var row := i + 1;
        var col := j + 1;
        if showBombs && field[i,j] {
          aux := "*";
        } else if IsOpen(row,col) {
          // convert rank (0..8) to a single digit string
          var r := GetRank(row,col);
          aux := DigitToString(r);
        } else if flagged[i,j] {
          aux := "?";
        }
        s := s + aux;
      }
      s := s + "\n";
    }
  }

  // Helper: convert small nat (0..8) to the corresponding string
  function DigitToString(n: nat): string
    requires n <= 9

  {
    if n == 0 then "0" else if n == 1 then "1"
    else if n == 2 then "2" else if n == 3 then "3"
    else if n == 4 then "4" else if n == 5 then "5"
    else if n == 6 then "6" else if n == 7 then "7"
    else if n == 8 then "8" else "9"
  }

} //end of class Minesweeper


/********************************************************************************************************* 
  Main with a simple demonstration of the use of the Minesweeper class 
**********************************************************************************************************/  

method Main ()
{
  
  // simulated input: sequence of actions and positions
  // uses "o" for open and "f" for flag/unflag
  // positions are given as (row,col) pairs
  // the two sequences of positions can be used to simulate a situation
  // where the user wins and another where the user hits a mine
  var inputAct: seq<string> := ["o", "o", "o", "o", "o", "o", "f", "f", "o"];
  var inputPos: seq<(nat,nat)> := [(3,1), (2,1), (3,2), (2,2), (3,3), (2,3), (1,1), (1,2), (1,3)];
                              // [(3,1), (1,1), (3,2), (2,2), (3,3), (2,3), (2,1), (1,2), (1,3)];
  var board := new Minesweeper(3,3,2);
  label loopStart:

  var i := 0;
  while i < |inputAct| && i < |inputPos| && board.IsAlive() && !board.Won() 
    invariant board.Repr == old@loopStart(board.Repr)
    invariant board.Valid()
    invariant 0 <= i <= |inputAct| 
    invariant 0 <= i <= |inputPos|
  {
    // get input
    if i < |inputAct| && i < |inputPos| {
      var (row,col) := inputPos[i];
      var cmd: string := inputAct[i];

      // print simulated input
      print "Action: "+ cmd + " on position (";
      print row; print ", "; print col; print ")\n";

      if cmd == "o" && board.IsPosition(row,col) && !board.IsOpen(row,col) {
        board.Open(row, col);
      } else if cmd == "f" && board.IsPosition(row,col) && !board.IsOpen(row,col){
        board.ToggleFlag(row, col);
      } else {
        print "Unknown command or invalid position.\n";
      }
      
      // print board
      var auxS := board.BoardToString();
      print "---\n"+auxS+"---\n";
    }
    i := i + 1;
  }
  // print state and final board
  if board.Won() {
    print "Congratulations! You've won the game!\n";
  } else if !board.IsAlive() {
    print "Game over! You've hit a mine.\n";
  }

  var auxS := board.BoardToString();
  print "---\n"+auxS+"---\n";
}



/********************************************************************************************************* 
  Test cases for the Minesweeper class
**********************************************************************************************************/  


// A test case, checked statically by Dafny, that covers the constructor 
method testConstructor()
{
  // create new game
  var board := new Minesweeper(5,5,2);

  assert board.Columns() == 5; 
  assert board.Lines() == 5;
  assert board.NumberOfMines() == 2;
  
  assert board.ExistsPositionToOpen();
  assert board.IsAlive();
  assert !board.Won();

  assert !board.IsOpen(1,1);
  assert !board.IsOpen(5,4);
  assert !board.IsFlagged(3,1);
  assert !board.IsFlagged(2,3);
}

 

// A test case, checked statically by Dafny, that covers the Open method 
method testOpen()
{
  // create new game
  var board := new Minesweeper(5,5,2);

  // open a cell
  board.Open(1,1);

  assert board.IsOpen(1,1);
  assert !board.IsOpen(5,4);

  assert !board.IsFlagged(3,1);
  assert !board.IsFlagged(2,3);

  assert board.Columns() == 5; 
  assert board.Lines() == 5;
  assert board.NumberOfMines() == 2;

  if board.HasMine(1,1) {
    assert !board.IsAlive();
    assert !board.Won();
  } 
  else {
    assert board.IsAlive();
    assert !board.Won() ==> board.ExistsPositionToOpen();
    // cannot conclude anything about Won() here
  }
}

/*
// A test case, to be checked statically by Dafny, that should fail
// because of incorrect call to the HasMine() method
method testFailHasMine()
{
  // create new game
  var board := new Minesweeper(5,5,2);
  // this one should fail the static analysis, because it
  // does not satisfy the requirement that in order to call HasMine()
  // the position has to be open or the game has to be won
  var b := board.HasMine(1,1);
}
*/


/*
// A test case, to be checked statically by Dafny, that should fail
// because of incorrect call to the Open() method
method testFailOpen()
{
  // create new game
  var board := new Minesweeper(5,5,2);

  // open a cell
  board.Open(1,1);

  // this one should fail the static analysis, because it
  // does not satisfy the precondition that a position that is already
  // open cannot be opened again
   board.Open(1,1);
}
*/

/*
// A test case, to be checked statically by Dafny, that should fail
// because of incorrect call to the ToggleFlag() method
method testFailToggleFlag()
{
  // create new game
  var board := new Minesweeper(5,5,2);

  // open a cell
  board.Open(1,1);

  // this one should fail the static analysis, because it
  // does not satisfy the precondition that a position that is already
  // open cannot be flagged or unflagged
   board.ToggleFlag(1,1);
}
*/


