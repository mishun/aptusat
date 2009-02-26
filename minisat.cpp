/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cassert>
#include <new>
#include <algorithm>
#include <stdexcept>
#include <vector>
#include <string>

namespace minisat {

//=================================================================================================
// Automatically resizable arrays
//
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)

template<class T>
class vec {
    T*  data;
    int sz;
    int cap;

    void     init(int size, const T& pad);
    void     grow(int min_cap);

    // Don't allow copying (error prone):
    vec<T>&  operator = (vec<T>& other) { assert(0); return *this; }
             vec        (vec<T>& other) { assert(0); }

    static inline int imin(int x, int y) {
        int mask = (x-y) >> (sizeof(int)*8-1);
        return (x&mask) + (y&(~mask)); }

    static inline int imax(int x, int y) {
        int mask = (y-x) >> (sizeof(int)*8-1);
        return (x&mask) + (y&(~mask)); }

public:
    // Types:
    typedef int Key;
    typedef T   Datum;

    // Constructors:
    vec(void)                   : data(NULL) , sz(0)   , cap(0)    { }
    vec(int size)               : data(NULL) , sz(0)   , cap(0)    { growTo(size); }
    vec(int size, const T& pad) : data(NULL) , sz(0)   , cap(0)    { growTo(size, pad); }
    vec(T* array, int size)     : data(array), sz(size), cap(size) { }      // (takes ownership of array -- will be deallocated with 'free()')
   ~vec(void)                                                      { clear(true); }

    // Ownership of underlying array:
    T*       release  (void)           { T* ret = data; data = NULL; sz = 0; cap = 0; return ret; }
    operator T*       (void)           { return data; }     // (unsafe but convenient)
    operator const T* (void) const     { return data; }

    // Size operations:
    int      size   (void) const       { return sz; }
    void     shrink (int nelems)       { assert(nelems <= sz); for (int i = 0; i < nelems; i++) sz--, data[sz].~T(); }
    void     shrink_(int nelems)       { assert(nelems <= sz); sz -= nelems; }
    void     pop    (void)             { sz--, data[sz].~T(); }
    void     growTo (int size);
    void     growTo (int size, const T& pad);
    void     clear  (bool dealloc = false);
    void     capacity (int size) { grow(size); }

    // Stack interface:
#if 1
    void     push  (void)              { if (sz == cap) { cap = imax(2, (cap*3+1)>>1); data = (T*)realloc(data, cap * sizeof(T)); } new (&data[sz]) T(); sz++; }
    //void     push  (const T& elem)     { if (sz == cap) { cap = imax(2, (cap*3+1)>>1); data = (T*)realloc(data, cap * sizeof(T)); } new (&data[sz]) T(elem); sz++; }
    void     push  (const T& elem)     { if (sz == cap) { cap = imax(2, (cap*3+1)>>1); data = (T*)realloc(data, cap * sizeof(T)); } data[sz++] = elem; }
    void     push_ (const T& elem)     { assert(sz < cap); data[sz++] = elem; }
#else
    void     push  (void)              { if (sz == cap) grow(sz+1); new (&data[sz]) T()    ; sz++; }
    void     push  (const T& elem)     { if (sz == cap) grow(sz+1); new (&data[sz]) T(elem); sz++; }
#endif

    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

    // Vector interface:
    const T& operator [] (int index) const  { return data[index]; }
    T&       operator [] (int index)        { return data[index]; }


    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const { copy.clear(); copy.growTo(sz); for (int i = 0; i < sz; i++) new (&copy[i]) T(data[i]); }
    void moveTo(vec<T>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }
};

template<class T>
void vec<T>::grow(int min_cap) {
    if (min_cap <= cap) return;
    if (cap == 0) cap = (min_cap >= 2) ? min_cap : 2;
    else          do cap = (cap*3+1) >> 1; while (cap < min_cap);
    data = (T*)realloc(data, cap * sizeof(T)); }

template<class T>
void vec<T>::growTo(int size, const T& pad) {
    if (sz >= size) return;
    grow(size);
    for (int i = sz; i < size; i++) new (&data[i]) T(pad);
    sz = size; }

template<class T>
void vec<T>::growTo(int size) {
    if (sz >= size) return;
    grow(size);
    for (int i = sz; i < size; i++) new (&data[i]) T();
    sz = size; }

template<class T>
void vec<T>::clear(bool dealloc) {
    if (data != NULL){
        for (int i = 0; i < sz; i++) data[i].~T();
        sz = 0;
        if (dealloc) free(data), data = NULL, cap = 0; } }



#if 1
template<class V, class T>
static inline void remove(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    assert(j < ts.size());
    for (; j < ts.size()-1; j++) ts[j] = ts[j+1];
    ts.pop();
}
#else
template<class V, class T>
static inline void remove(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    assert(j < ts.size());
    ts[j] = ts.last();
    ts.pop();
}
#endif

template<class V, class T>
static inline bool find(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    return j < ts.size();
}

//=================================================================================================
// A heap implementation with support for decrease/increase key.


template<class Comp>
class Heap {
    Comp     lt;
    vec<int> heap;     // heap of ints
    vec<int> indices;  // int -> index in heap

    // Index "traversal" functions
    static inline int left  (int i) { return i*2+1; }
    static inline int right (int i) { return (i+1)*2; }
    static inline int parent(int i) { return (i-1) >> 1; }


    inline void percolateUp(int i)
    {
        int x = heap[i];
        while (i != 0 && lt(x, heap[parent(i)])){
            heap[i]          = heap[parent(i)];
            indices[heap[i]] = i;
            i                = parent(i);
        }
        heap   [i] = x;
        indices[x] = i;
    }


    inline void percolateDown(int i)
    {
        int x = heap[i];
        while (left(i) < heap.size()){
            int child = right(i) < heap.size() && lt(heap[right(i)], heap[left(i)]) ? right(i) : left(i);
            if (!lt(heap[child], x)) break;
            heap[i]          = heap[child];
            indices[heap[i]] = i;
            i                = child;
        }
        heap   [i] = x;
        indices[x] = i;
    }


    bool heapProperty (int i) const {
        return i >= heap.size()
            || ((i == 0 || !lt(heap[i], heap[parent(i)])) && heapProperty(left(i)) && heapProperty(right(i))); }


  public:
    Heap(const Comp& c) : lt(c) { }

    int  size      ()          const { return heap.size(); }
    bool empty     ()          const { return heap.size() == 0; }
    bool inHeap    (int n)     const { return n < indices.size() && indices[n] >= 0; }
    int  operator[](int index) const { assert(index < heap.size()); return heap[index]; }

    void decrease  (int n) { assert(inHeap(n)); percolateUp(indices[n]); }

    // RENAME WHEN THE DEPRECATED INCREASE IS REMOVED.
    void increase_ (int n) { assert(inHeap(n)); percolateDown(indices[n]); }


    void insert(int n)
    {
        indices.growTo(n+1, -1);
        assert(!inHeap(n));

        indices[n] = heap.size();
        heap.push(n);
        percolateUp(indices[n]); 
    }


    int  removeMin()
    {
        int x            = heap[0];
        heap[0]          = heap.last();
        indices[heap[0]] = 0;
        indices[x]       = -1;
        heap.pop();
        if (heap.size() > 1) percolateDown(0);
        return x; 
    }


    void clear(bool dealloc = false) 
    { 
        for (int i = 0; i < heap.size(); i++)
            indices[heap[i]] = -1;
        heap.clear(dealloc); 
    }


    // Fool proof variant of insert/decrease/increase
    void update (int n)
    {
        if (!inHeap(n))
            insert(n);
        else {
            percolateUp(indices[n]);
            percolateDown(indices[n]);
        }
    }


    // Delete elements from the heap using a given filter function (-object).
    // *** this could probaly be replaced with a more general "buildHeap(vec<int>&)" method ***
    template <class F>
    void filter(const F& filt) {
        int i,j;
        for (i = j = 0; i < heap.size(); i++)
            if (filt(heap[i])){
                heap[j]          = heap[i];
                indices[heap[i]] = j++;
            }else
                indices[heap[i]] = -1;

        heap.shrink(i - j);
        for (int i = heap.size() / 2 - 1; i >= 0; i--)
            percolateDown(i);

        assert(heapProperty());
    }


    // DEBUG: consistency checking
    bool heapProperty() const {
        return heapProperty(1); }


    // COMPAT: should be removed
    void setBounds (int n) { }
    void increase  (int n) { decrease(n); }
    int  getmin    ()      { return removeMin(); }

};


//=================================================================================================


//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)


class Lit {
    int     x;
 public:
    Lit() : x(2*var_Undef)                                              { }   // (lit_Undef)
    explicit Lit(Var var, bool sign = false) : x((var+var) + (int)sign) { }

    // Don't use these for constructing/deconstructing literals. Use the normal constructors instead.
    friend int  toInt       (Lit p);  // Guarantees small, positive integers suitable for array indexing.
    friend Lit  toLit       (int i);  // Inverse of 'toInt()'
    friend Lit  operator   ~(Lit p);
    friend bool sign        (Lit p);
    friend int  var         (Lit p);
    friend Lit  unsign      (Lit p);
    friend Lit  id          (Lit p, bool sgn);

    bool operator == (Lit p) const { return x == p.x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' guarantees that p, ~p are adjacent in the ordering.
};

inline  int  toInt       (Lit p)           { return p.x; }
inline  Lit  toLit       (int i)           { Lit p; p.x = i; return p; }
inline  Lit  operator   ~(Lit p)           { Lit q; q.x = p.x ^ 1; return q; }
inline  bool sign        (Lit p)           { return p.x & 1; }
inline  int  var         (Lit p)           { return p.x >> 1; }
inline  Lit  unsign      (Lit p)           { Lit q; q.x = p.x & ~1; return q; }
inline  Lit  id          (Lit p, bool sgn) { Lit q; q.x = p.x ^ (int)sgn; return q; }

const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
const Lit lit_Error(var_Undef, true );  // }


//=================================================================================================
// Lifted booleans:


class lbool {
    char     value;
    explicit lbool(int v) : value(v) { }

public:
    lbool()       : value(0) { }
    lbool(bool x) : value((int)x*2-1) { }
    int toInt(void) const { return value; }

    bool  operator == (lbool b) const { return value == b.value; }
    bool  operator != (lbool b) const { return value != b.value; }
    lbool operator ^ (bool b) const { return b ? lbool(-value) : lbool(value); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.toInt(); }
inline lbool toLbool(int   v) { return lbool(v);  }

const lbool l_True  = toLbool( 1);
const lbool l_False = toLbool(-1);
const lbool l_Undef = toLbool( 0);

//=================================================================================================
// Clause -- a simple class for representing a clause:


class Clause {
    uint32_t size_etc;
    union { float act; uint32_t abst; } extra;
    Lit     data[0];

public:
    void calcAbstraction() {
        uint32_t abstraction = 0;
        for (int i = 0; i < size(); i++)
            abstraction |= 1 << (var(data[i]) & 31);
        extra.abst = abstraction;  }

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    Clause(const V& ps, bool learnt) {
        size_etc = (ps.size() << 3) | (uint32_t)learnt;
        for (int i = 0; i < ps.size(); i++) data[i] = ps[i];
        if (learnt) extra.act = 0; else calcAbstraction(); }

    // -- use this function instead:
    template<class V>
    friend Clause* Clause_new(const V& ps, bool learnt = false) {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
        void* mem = malloc(sizeof(Clause) + sizeof(uint32_t)*(ps.size()));
        return new (mem) Clause(ps, learnt); }

    int          size        ()      const   { return size_etc >> 3; }
    void         shrink      (int i)         { assert(i <= size()); size_etc = (((size_etc >> 3) - i) << 3) | (size_etc & 7); }
    void         pop         ()              { shrink(1); }
    bool         learnt      ()      const   { return size_etc & 1; }
    uint32_t     mark        ()      const   { return (size_etc >> 1) & 3; }
    void         mark        (uint32_t m)    { size_etc = (size_etc & ~6) | ((m & 3) << 1); }
    const Lit&   last        ()      const   { return data[size()-1]; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Lit&         operator [] (int i)         { return data[i]; }
    Lit          operator [] (int i) const   { return data[i]; }
    operator const Lit* (void) const         { return data; }

    float&       activity    ()              { return extra.act; }
    uint32_t     abstraction () const { return extra.abst; }

    Lit          subsumes    (const Clause& other) const;
    void         strengthen  (Lit p);
};


/*_________________________________________________________________________________________________
|
|  subsumes : (other : const Clause&)  ->  Lit
|  
|  Description:
|       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
|       by subsumption resolution.
|  
|    Result:
|       lit_Error  - No subsumption or simplification
|       lit_Undef  - Clause subsumes 'other'
|       p          - The literal p can be deleted from 'other'
|________________________________________________________________________________________________@*/
inline Lit Clause::subsumes(const Clause& other) const
{
    if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
        return lit_Error;

    Lit        ret = lit_Undef;
    const Lit* c  = (const Lit*)(*this);
    const Lit* d  = (const Lit*)other;

    for (int i = 0; i < size(); i++) {
        // search for c[i] or ~c[i]
        for (int j = 0; j < other.size(); j++)
            if (c[i] == d[j])
                goto ok;
            else if (ret == lit_Undef && c[i] == ~d[j]){
                ret = c[i];
                goto ok;
            }

        // did not find it
        return lit_Error;
    ok:;
    }

    return ret;
}


inline void Clause::strengthen(Lit p)
{
    remove(*this, p);
    calcAbstraction();
}


//=================================================================================================
// Solver -- the main class:


class Solver {
public:

    // Constructor/Destructor:
    //
    Solver();
    ~Solver();

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.
    bool    addClause (vec<Lit>& ps);                           // Add a clause to the solver. NOTE! 'ps' may be shrunk by this method!

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    bool    solve        ();                        // Search without assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    // Variable mode:
    // 
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    double    var_decay;          // Inverse of the variable activity decay factor.                                            (default 1 / 0.95)
    double    clause_decay;       // Inverse of the clause activity decay factor.                                              (1 / 0.999)
    double    random_var_freq;    // The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02)
    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
    bool      expensive_ccmin;    // Controls conflict clause minimization.                                                    (default TRUE)
    int       polarity_mode;      // Controls which polarity the decision heuristic chooses. See enum below for allowed modes. (default polarity_false)
    int       verbosity;          // Verbosity level. 0=silent, 1=some progress report                                         (default 0)

    enum { polarity_true = 0, polarity_false = 1, polarity_user = 2, polarity_rnd = 3 };

    // Statistics: (read-only member variable)
    //
    uint64_t starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t clauses_literals, learnts_literals, max_literals, tot_literals;

protected:

    // Helper structures:
    //
    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    friend class VarFilter;
    struct VarFilter {
        const Solver& s;
        VarFilter(const Solver& _s) : s(_s) {}
        bool operator()(Var v) const { return toLbool(s.assigns[v]) == l_Undef && s.decision_var[v]; }
    };

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<Clause*>        clauses;          // List of problem clauses.
    vec<Clause*>        learnts;          // List of learnt clauses.
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    vec<vec<Clause*> >  watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<char>           assigns;          // The current assignments (lbool:s stored as char:s).
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision_var;     // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<Clause*>        reason;           // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
    vec<int>            level;            // 'level[var]' contains the level at which the assignment was made.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              random_seed;      // Used by the random variable selection.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    (int polarity_mode, double random_var_freq);             // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, Clause* from = NULL);                            // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, Clause* from = NULL);                            // Test if fact 'p' contradicts current state, enqueue otherwise.
    Clause*  propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (Clause* confl, vec<Lit>& out_learnt, int& out_btlevel); // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int nof_conflicts, int nof_learnts);                    // Search for a given number of conflicts.
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<Clause*>& cs);                                      // Shrink 'cs' to contain only non-satisfied clauses.

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (Clause& c);             // Attach a clause to watcher lists.
    void     detachClause     (Clause& c);             // Detach a clause to watcher lists.
    void     removeClause     (Clause& c);             // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...

    // Debug:
    void     printLit         (Lit l);
    template<class C>
    void     printClause      (const C& c);
    void     verifyModel      ();
    void     checkLiteralCount();

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }
};


//=================================================================================================
// Implementation of inline methods:


inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision_var[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() { var_inc *= var_decay; }
inline void Solver::varBumpActivity(Var v) {
    if ( (activity[v] += var_inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= clause_decay; }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                learnts[i]->activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline bool     Solver::enqueue         (Lit p, Clause* from)   { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::locked          (const Clause& c) const { return reason[var(c[0])] == &c && value(c[0]) == l_True; }
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level[x] & 31); }
inline lbool    Solver::value         (Var x) const   { return toLbool(assigns[x]); }
inline lbool    Solver::value         (Lit p) const   { return toLbool(assigns[var(p)]) ^ sign(p); }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts.size(); }
inline int      Solver::nVars         ()      const   { return assigns.size(); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity    [v] = (char)b; }
inline void     Solver::setDecisionVar(Var v, bool b) { decision_var[v] = (char)b; if (b) { insertVarOrder(v); } }
inline bool     Solver::solve         ()              { vec<Lit> tmp; return solve(tmp); }
inline bool     Solver::okay          ()      const   { return ok; }



//=================================================================================================
// Debug + etc:


#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )

static inline void logLit(FILE* f, Lit l)
{
    fprintf(f, "%sx%d", sign(l) ? "~" : "", var(l)+1);
}

static inline void logLits(FILE* f, const vec<Lit>& ls)
{
    fprintf(f, "[ ");
    if (ls.size() > 0){
        logLit(f, ls[0]);
        for (int i = 1; i < ls.size(); i++){
            fprintf(f, ", ");
            logLit(f, ls[i]);
        }
    }
    fprintf(f, "] ");
}

static inline const char* showBool(bool b) { return b ? "true" : "false"; }


// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(bool expr) { assert(expr); }


inline void Solver::printLit(Lit l)
{
    reportf("%s%d:%c", sign(l) ? "-" : "", var(l)+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}


template<class C>
inline void Solver::printClause(const C& c)
{
    for (int i = 0; i < c.size(); i++){
        printLit(c[i]);
        fprintf(stderr, " ");
    }
}




//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters: (formerly in 'SearchParams')
    var_decay(1 / 0.95), clause_decay(1 / 0.999), random_var_freq(0.02)
  , restart_first(100), restart_inc(1.5), learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // More parameters:
    //
  , expensive_ccmin  (true)
  , polarity_mode    (polarity_false)
  , verbosity        (0)

    // Statistics: (formerly in 'SolverStats')
    //
  , starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok               (true)
  , cla_inc          (1)
  , var_inc          (1)
  , qhead            (0)
  , simpDB_assigns   (-1)
  , simpDB_props     (0)
  , order_heap       (VarOrderLt(activity))
  , random_seed      (91648253)
  , progress_estimate(0)
  , remove_satisfied (true)
{}


Solver::~Solver()
{
    for (int i = 0; i < learnts.size(); i++) free(learnts[i]);
    for (int i = 0; i < clauses.size(); i++) free(clauses[i]);
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    reason    .push(NULL);
    assigns   .push(toInt(l_Undef));
    level     .push(-1);
    activity  .push(0);
    seen      .push(0);

    polarity    .push((char)sign);
    decision_var.push((char)dvar);

    insertVarOrder(v);
    return v;
}


bool Solver::addClause(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);

    if (!ok)
        return false;
    else{
        // Check if clause is satisfied and remove false/duplicate literals:
        std::sort((Lit *)ps, (Lit *)ps + ps.size());
        Lit p; int i, j;
        for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
            if (value(ps[i]) == l_True || ps[i] == ~p)
                return true;
            else if (value(ps[i]) != l_False && ps[i] != p)
                ps[j++] = p = ps[i];
        ps.shrink(i - j);
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        assert(value(ps[0]) == l_Undef);
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == NULL);
    }else{
        Clause* c = Clause_new(ps, false);
        clauses.push(c);
        attachClause(*c);
    }

    return true;
}


void Solver::attachClause(Clause& c) {
    assert(c.size() > 1);
    watches[toInt(~c[0])].push(&c);
    watches[toInt(~c[1])].push(&c);
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::detachClause(Clause& c) {
    assert(c.size() > 1);
    assert(find(watches[toInt(~c[0])], &c));
    assert(find(watches[toInt(~c[1])], &c));
    remove(watches[toInt(~c[0])], &c);
    remove(watches[toInt(~c[1])], &c);
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(Clause& c) {
    detachClause(c);
    free(&c); }


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var     x  = var(trail[c]);
            assigns[x] = toInt(l_Undef);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit(int polarity_mode, double random_var_freq)
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (toLbool(assigns[next]) == l_Undef && decision_var[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || toLbool(assigns[next]) != l_Undef || !decision_var[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    bool sign = false;
    switch (polarity_mode){
    case polarity_true:  sign = false; break;
    case polarity_false: sign = true;  break;
    case polarity_user:  sign = polarity[next]; break;
    case polarity_rnd:   sign = irand(random_seed, 2); break;
    default: assert(false); }

    return next == var_Undef ? lit_Undef : Lit(next, sign);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|  
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void Solver::analyze(Clause* confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    do{
        assert(confl != NULL);          // (otherwise should be UIP)
        Clause& c = *confl;

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level[var(q)] > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level[var(q)] >= decisionLevel())
                    pathC++;
                else{
                    out_learnt.push(q);
                    if (level[var(q)] > out_btlevel)
                        out_btlevel = level[var(q)];
                }
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason[var(p)];
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    if (expensive_ccmin){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[var(out_learnt[i])] == NULL || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
    }else{
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++){
            Clause& c = *reason[var(out_learnt[i])];
            for (int k = 1; k < c.size(); k++)
                if (!seen[var(c[k])] && level[var(c[k])] > 0){
                    out_learnt[j++] = out_learnt[i];
                    break; }
        }
    }
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        for (int i = 2; i < out_learnt.size(); i++)
            if (level[var(out_learnt[i])] > level[var(out_learnt[max_i])])
                max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level[var(p)];
    }


    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason[var(analyze_stack.last())] != NULL);
        Clause& c = *reason[var(analyze_stack.last())]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level[var(p)] > 0){
                if (reason[var(p)] != NULL && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason[x] == NULL){
                assert(level[x] > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = *reason[x];
                for (int j = 1; j < c.size(); j++)
                    if (level[var(c[j])] > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, Clause* from)
{
    assert(value(p) == l_Undef);
    assigns [var(p)] = toInt(lbool(!sign(p)));  // <<== abstract but not uttermost effecient
    level   [var(p)] = decisionLevel();
    reason  [var(p)] = from;
    trail.push(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause* Solver::propagate()
{
    Clause* confl     = NULL;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Clause*>&  ws  = watches[toInt(p)];
        Clause         **i, **j, **end;
        num_props++;

        for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
            Clause& c = **i++;

            // Make sure the false literal is data[1]:
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            if (value(first) == l_True){
                *j++ = &c;
            }else{
                // Look for new watch:
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[toInt(~c[1])].push(&c);
                        goto FoundWatch; }

                // Did not find watch -- clause is unit under assignment:
                *j++ = &c;
                if (value(first) == l_False){
                    confl = &c;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }else
                    uncheckedEnqueue(first, &c);
            }
        FoundWatch:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { bool operator () (Clause* x, Clause* y) { return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity()); } };
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

//    sort(learnts, reduceDB_lt());
    std::sort((Clause **)learnts, (Clause **)learnts + learnts.size(), reduceDB_lt());

    for (i = j = 0; i < learnts.size() / 2; i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]))
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++){
        if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() < extra_lim)
            removeClause(*learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
}


void Solver::removeSatisfied(vec<Clause*>& cs)
{
    int i,j;
    for (i = j = 0; i < cs.size(); i++){
        if (satisfied(*cs[i]))
            removeClause(*cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != NULL)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts, int nof_learnts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

    bool first = true;

    for (;;){
        Clause* confl = propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                Clause* c = Clause_new(learnt_clause, true);
                learnts.push(c);
                attachClause(*c);
                claBumpActivity(*c);
                uncheckedEnqueue(learnt_clause[0], c);
            }

            varDecayActivity();
            claDecayActivity();

        }else{
            // NO CONFLICT

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}


bool Solver::solve(const vec<Lit>& assumps)
{
    model.clear();
    conflict.clear();

    if (!ok) return false;

    assumps.copyTo(assumptions);

    double  nof_conflicts = restart_first;
    double  nof_learnts   = nClauses() * learntsize_factor;
    lbool   status        = l_Undef;

    if (verbosity >= 1){
        reportf("============================[ Search Statistics ]==============================\n");
        reportf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        reportf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        reportf("===============================================================================\n");
    }

    // Search:
    while (status == l_Undef){
        if (verbosity >= 1)
            reportf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, order_heap.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
        status = search((int)nof_conflicts, (int)nof_learnts);
        nof_conflicts *= restart_inc;
        nof_learnts   *= learntsize_inc;
    }

    if (verbosity >= 1)
        reportf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
#ifndef NDEBUG
        verifyModel();
#endif
    }else{
        assert(status == l_False);
        if (conflict.size() == 0)
            ok = false;
    }

    cancelUntil(0);
    return status == l_True;
}

//=================================================================================================
// Debug methods:


void Solver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++){
        assert(clauses[i]->mark() == 0);
        Clause& c = *clauses[i];
        for (int j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        reportf("unsatisfied clause: ");
        printClause(*clauses[i]);
        reportf("\n");
        failed = true;
    next:;
    }

    assert(!failed);

    reportf("Verified %d original clauses.\n", clauses.size());
}


void Solver::checkLiteralCount()
{
    // Check that sizes are calculated correctly:
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 0)
            cnt += clauses[i]->size();

    if ((int)clauses_literals != cnt){
        fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
        assert((int)clauses_literals == cnt);
    }
}

}





























std::string toString(int x)
{
	char buf[16];
	itoa(x, buf, 10);
	return buf;
}

template<class Comp>
class Heap
{
private:
	Comp     lt;
	std::vector<int> heap;
	std::vector<int> indices;

	static inline unsigned left(unsigned i) { return i * 2 + 1; }
	static inline unsigned right(unsigned i) { return (i + 1) * 2; }
	static inline unsigned parent(unsigned i) { return (i - 1) >> 1; }

	inline void percolateUp(unsigned i)
	{
		int x = heap[i];
		while(i != 0 && lt(x, heap[parent(i)]))
		{
			heap[i] = heap[parent(i)];
			indices[heap[i]] = i;
			i = parent(i);
		}
		heap[i] = x;
		indices[x] = i;
	}

	inline void percolateDown(unsigned i)
	{
		int x = heap[i];
		while(left(i) < heap.size())
		{
			int child = right(i) < heap.size() && lt(heap[right(i)], heap[left(i)]) ? right(i) : left(i);
			if(!lt(heap[child], x)) break;
			heap[i] = heap[child];
			indices[heap[i]] = i;
			i = child;
		}
		heap[i] = x;
		indices[x] = i;
	}

	bool heapProperty(unsigned i) const
	{
		return i >= heap.size() || ((i == 0 || !lt(heap[i], heap[parent(i)])) && heapProperty(left(i)) && heapProperty(right(i)));
	}

public:
	Heap(const Comp& c) : lt(c) {}

	unsigned size() const { return heap.size(); }
	bool empty() const { return heap.size() == 0; }
	bool inHeap(unsigned n) const { return n < indices.size() && indices[n] >= 0; }

	int operator[](unsigned index) const
	{
		assert(index < heap.size());
		return heap[index];
	}

	void decrease(int n) { assert(inHeap(n)); percolateUp(indices[n]); }

	void insert(int n)
	{
		if(n >= (int)indices.size())
			indices.resize(n + 1, -1);
		assert(!inHeap(n));
		indices[n] = heap.size();
		heap.push_back(n);
		percolateUp(indices[n]); 
	}

	int removeMin()
	{
		int x = heap[0];
		heap[0] = heap[heap.size() - 1];
		indices[heap[0]] = 0;
		indices[x] = -1;
		heap.pop_back();
		if(heap.size() > 1) percolateDown(0);
		return x; 
	}

	void clear()
	{ 
		for (int i = 0; i < heap.size(); i++)
			indices[heap[i]] = -1;
		heap.clear();
	}

	void update(int n)
	{
		if(!inHeap(n)) insert(n);
		else
		{
			percolateUp(indices[n]);
			percolateDown(indices[n]);
		}
	}

	template <class F>
	void filter(const F& filt)
	{
		unsigned i, j;
		for(i = j = 0; i < heap.size(); i++)
			if(filt(heap[i]))
			{
				heap[j] = heap[i];
				indices[heap[i]] = j++;
			}
			else indices[heap[i]] = -1;

		heap.resize(j);
		for(int i = heap.size() / 2 - 1; i >= 0; i--)
			percolateDown(i);
		assert(heapProperty());
	}

	bool heapProperty() const
	{
		return heapProperty(1);
	}
};

template<class V, class T>
static inline void remove(V& ts, const T& t)
{
	int j = 0;
	for (; j < ts.size() && ts[j] != t; j++);
	assert(j < ts.size());
	for (; j < ts.size()-1; j++) ts[j] = ts[j+1];
	ts.pop();
}

template<class V, class T>
static inline void remove_vector(V& ts, const T& t)
{
	unsigned j = 0;
	for(; j < ts.size() && ts[j] != t; j++);
	assert(j < ts.size());
	for(; j < ts.size()-1; j++) ts[j] = ts[j+1];
	ts.pop_back();
}

template<class V, class T>
static inline bool find(V& ts, const T& t)
{
	unsigned j = 0;
	for( ; j < ts.size() && ts[j] != t; j++);
	return j < ts.size();
}

//=================================================================================================
#undef var_Undef
const unsigned varUndef = 0xFFFFFFFF;

class Bool
{
public:
	Bool() : value(UNDEF.value) {}
	Bool(bool x) : value(x ? TRUE.value : FALSE.value) {}
	bool operator==(Bool b) const { return value == b.value; }
	bool operator!=(Bool b) const { return value != b.value; }
	Bool operator^(bool b) const { return b ? Bool(-value) : Bool(value); }

	std::string toString() const
	{
		if(*this == TRUE) return "TRUE";
		if(*this == FALSE) return "FALSE";
		return "UNDEF";
	}
private:
	Bool(int v) : value(v) {}
private:
	char value;
public:
	static const Bool TRUE;
	static const Bool FALSE;
	static const Bool UNDEF;
};

const Bool Bool::TRUE(1);
const Bool Bool::FALSE(-1);
const Bool Bool::UNDEF(0);


class Literal
{
public:
	Literal() : x(varUndef << 1) {}
	explicit Literal(unsigned var, bool sign = false) : x(var + var + (unsigned)sign) {}
	bool operator==(Literal p) const { return x == p.x; }
	bool operator!=(Literal p) const { return x != p.x; }
	bool operator<(Literal p) const { return x < p.x; }
	unsigned offset() const { return x; }
	bool sign() const { return (bool)(x & 1); }
	unsigned var() const { return x >> 1; }

	Literal operator~() const
	{
		Literal res;
		res.x = x ^ 1;
		return res;
	}

	std::string toString() const
	{
		if(*this == UNDEF) return "UNDEF";
		if(*this == ERROR) return "ERROR";
		if(sign()) return "~x" + ::toString(var() + 1);
		else return "x" + ::toString(var() + 1);
	}
private:
	unsigned x;
public:
	static const Literal UNDEF;
	static const Literal ERROR;
};

const Literal Literal::UNDEF(varUndef, false);
const Literal Literal::ERROR(varUndef, true);


class Clause
{
private:
	Clause(const std::vector<Literal> & ps, bool learnt) : sz(ps.size()), flags((ps.size() << 3) | (unsigned)learnt)
	{
		for(unsigned i = 0; i < ps.size(); i++)
			data[i] = ps[i];
		if(learnt) extra.act = 0;
		else calcAbstraction();
	}
public:
	friend Clause * Clause_new(const std::vector<Literal> & ps, bool learnt = false)
	{
		void * mem = malloc(sizeof(Clause) + sizeof(Literal) * ps.size());
		return new(mem) Clause(ps, learnt);
	}

	unsigned size() const { return sz; }
	const Literal & last() const { return data[size() - 1]; }
	Literal operator[](unsigned index) const { return data[index]; }
	bool learnt() const { return (bool)(flags & 1); }
	unsigned mark() const { return (flags >> 1) & 3; }

	Literal & operator[](unsigned index) { return data[index]; }
	void mark(unsigned m) { flags = (flags & ~6) | ((m & 3) << 1); }

	void calcAbstraction()
	{
		unsigned abstraction = 0;
		for(unsigned i = 0; i < size(); i++)
			abstraction |= 1 << (data[i].var() & 31);
		extra.abst = abstraction;
	}

	float & activity() { return extra.act; }
	unsigned abstraction() const { return extra.abst; }

	std::string toString() const
	{
		std::string res = "[";
		for(unsigned i = 0; i < (unsigned)size(); i++)
		{
			if(i != 0) res += "|";
			res += data[i].toString();
		}
		return res + "]";
	}
private:
	unsigned sz;
	unsigned flags;
	union { float act; unsigned abst; } extra;
	Literal data[0];
};


class Random
{
public:
	Random(unsigned init) : seed(init) {}

	double drand()
	{
		seed *= 1389796;
 		int q = (int)(seed / 2147483647);
		seed -= (double)q * 2147483647;
		return seed / 2147483647;
	}

	int irand(int size)
	{
		return (int)(drand() * size);
        }

private:
	double seed;
};


class Argument
{
public:
	Argument(unsigned vars) : x(vars, Bool::UNDEF) {}

	Bool operator[](Literal index) const { return x[index.var()] ^ index.sign(); }
	Bool operator[](unsigned index) const { return x[index]; }

	void set(unsigned index, Bool val) { x[index] = val; }
private:
	std::vector<Bool> x;
};


class VarSelector
{
public:
	explicit VarSelector(unsigned vars)
		: variables(vars)
		, random(91648253)
		, heap(VarOrderLt(activity))
		, activity(vars, 0)
		, decision_var(vars, true)
		, polarity(vars, true)
		, increment(1)
		, decay(1 / 0.95)
		, random_var_freq(0.02)
		, rnd_decisions(0)
		, polarity_mode(polarity_false)
	{
		for(unsigned v = 0; v < variables; v++)
			insertVarOrder(v);
	}

	unsigned size() const
	{
		return heap.size();
	}

	Literal getBranchLiteral(const Argument & assigns)
	{
		unsigned next = varUndef;

		// Random decision:
		if(random.drand() < random_var_freq && !heap.empty())
		{
			next = heap[ random.irand(heap.size()) ];
			if(assigns[next] == Bool::UNDEF && decision_var[next])
				rnd_decisions++;
		}

		// Activity based decision:
		while(next == varUndef || assigns[next] != Bool::UNDEF || !decision_var[next])
			if(heap.empty())
			{
				next = varUndef;
				break;
			}
			else next = heap.removeMin();

		bool sign = false;
		switch(polarity_mode)
		{
		case polarity_true:
			sign = false;
			break;
		case polarity_false:
			sign = true;
			break;
		case polarity_user:
			sign = polarity[next];
			break;
		case polarity_rnd:
			sign = random.irand(2);
			break;
		default:
			assert(false);
		}

		return next == varUndef ? Literal::UNDEF : Literal(next, sign);
	}

	// Insert a variable in the decision order priority queue.
	void insertVarOrder(unsigned x)
	{
		assert(x < variables);
		if(!heap.inHeap(x) && decision_var[x])
			heap.insert(x);
	}

	// Declare if a variable should be eligible for selection in the decision heuristic.
	void setDecisionVar(unsigned v, bool b)
	{
		assert(v < variables);
		assert(false);
		decision_var[v] = b;
		if(b) insertVarOrder(v);
	}

	// Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
	void setPolarity(unsigned v, bool b)
	{
		assert(v < variables);
		polarity[v] = (char)b;
	}

	// Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
	void decayActivity()
	{
		increment *= decay;
	}

	// Increase a variable with the current 'bump' value.
	void bumpActivity(unsigned v)
	{
		assert(v < variables);

		if((activity[v] += increment) > 1e100)
		{
			// Rescale:
			for(unsigned i = 0; i < variables; i++)
				activity[i] *= 1e-100;
			increment *= 1e-100;
		}

		// Update order_heap with respect to new activity:
		if(heap.inHeap(v))
			heap.decrease(v);
	}

	void filter(const Argument & assigns)
	{
		heap.filter(VarFilter(*this, assigns));
	}

private:
	friend class VarFilter;
	struct VarFilter
	{
		const VarSelector & s;
		const Argument & assigns;

		VarFilter(const VarSelector & _s, const Argument & _a) : s(_s), assigns(_a) {}
		bool operator()(unsigned v) const { return assigns[v] == Bool::UNDEF && s.decision_var[v]; }
	};

	struct VarOrderLt
	{
		const std::vector<double> & activity;
		bool operator()(unsigned x, unsigned y) const { return activity[x] > activity[y]; }
		VarOrderLt(const std::vector<double> & act) : activity(act) {}
	};

	enum { polarity_true = 0, polarity_false = 1, polarity_user = 2, polarity_rnd = 3 };

private:
	const unsigned variables;
	Random random;
	Heap<VarOrderLt> heap;          // A priority queue of variables ordered with respect to the variable activity.
	std::vector<double> activity;   // A heuristic measurement of the activity of a variable.
	std::vector<bool> decision_var; // Declares if a variable is eligible for selection in the decision heuristic.
	std::vector<bool> polarity;     // The preferred polarity of each variable.
	double increment;               // Amount to bump next variable with.
	double decay; 	                // Inverse of the variable activity decay factor.                                            (default 1 / 0.95)
	double random_var_freq;         // The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02)
	unsigned long long rnd_decisions;
	int polarity_mode;              // Controls which polarity the decision heuristic chooses. See enum below for allowed modes. (default polarity_false)
};


class CNFFormula
{
};


class SATSolver
{
public:
	SATSolver(unsigned, const std::vector< std::vector<int> > &);
	~SATSolver();
	bool sat();
	std::vector<bool> getSolution() { return solution; }

public:
	const unsigned variables;

private:
	std::vector<bool> solution;

	std::vector< std::vector<Clause *> > watches;  // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
	std::vector<Literal> trail;            // Assignment stack; stores all assigments made in the order they were made.
	std::vector<int> trail_lim;            // Separator indices for different decision levels in 'trail'.
	std::vector<Literal> assumptions;      // Current set of assumptions provided to solve by the user.
	std::vector<Bool> model;               // If problem is satisfiable, this vector contains the model (if any).
	std::vector<Literal> conflict;         // If problem is unsatisfiable (possibly under assumptions),
                                               // this vector represent the final conflict clause expressed in the assumptions.

	std::vector<Clause *> clauses;         // List of problem clauses.
	std::vector<Clause *> learnts;         // List of learnt clauses.
	std::vector<Clause *> reason;          // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
	std::vector<int> level;                // 'level[var]' contains the level at which the assignment was made.

	std::vector<char> seen;
	std::vector<Literal> analyze_stack;  
	std::vector<Literal> analyze_toclear;
	std::vector<Literal> add_tmp;

	bool ok;
	Argument assigns;
	VarSelector var_sel;

protected:
	bool addClause(std::vector<Literal> &);
	void removeSatisfied(std::vector<Clause *> &);
	bool simplify();                                           // Removes already satisfied clauses.
	bool solve(const std::vector<Literal> & = std::vector<Literal>()); // Search for a model that respects a given set of assumptions.

	unsigned nAssigns() const { return trail.size(); }          // The current number of assigned literals.
	unsigned nClauses() const { return clauses.size(); }        // The current number of original clauses. 
	unsigned nLearnts() const { return learnts.size(); }        // The current number of learnt clauses.   
	unsigned decisionLevel() const { return trail_lim.size(); } // Gives the current decisionlevel.
	void newDecisionLevel() { trail_lim.push_back(trail.size()); }          // Begins a new decision level.
	uint32_t abstractLevel(unsigned x) const { return 1 << (level[x] & 31); }   // Used to represent an abstraction of sets of decision levels.
	Bool modelValue(Literal p) const { return model[p.var()] ^ p.sign(); }       // The value of a literal in the last model. The last call to solve must have been satisfiable.

	void claDecayActivity() { cla_inc *= clause_decay; } // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
	void claBumpActivity(Clause & c)                     // Increase a clause with the current 'bump' value.
	{
		if((c.activity() += cla_inc) > 1e20)
		{
			for(unsigned i = 0; i < learnts.size(); i++)
				learnts[i]->activity() *= 1e-20;
			cla_inc *= 1e-20;
		}
	}

	bool enqueue(Literal p, Clause* from = NULL) // Test if fact 'p' contradicts current state, enqueue otherwise.
	{
		return assigns[p] != Bool::UNDEF ? assigns[p] != Bool::FALSE : (uncheckedEnqueue(p, from), true);
	}

	bool locked(const Clause & c) const      // Returns TRUE if a clause is a reason for some implication in the current state.
	{
		return reason[c[0].var()] == &c && assigns[c[0]] == Bool::TRUE;
	}

public:
	// Mode of operation:
	double clause_decay;      // Inverse of the clause activity decay factor.                                              (1 / 0.999)
	int restart_first;        // The initial restart limit.                                                                (default 100)
	double restart_inc;       // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
	double learntsize_factor; // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
	double learntsize_inc;    // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
	bool expensive_ccmin;     // Controls conflict clause minimization.                                                    (default TRUE)
	int verbosity;            // Verbosity level. 0=silent, 1=some progress report                                         (default 0)

	// Statistics: (read-only member variable)
	uint64_t starts, decisions, propagations, conflicts;
	uint64_t clauses_literals, learnts_literals, max_literals, tot_literals;

protected:
	double  cla_inc;          // Amount to bump next clause with.
	int     qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
	int     simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
	int64_t simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
	double  progress_estimate;// Set by 'search()'.
	bool    remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

	void     uncheckedEnqueue(Literal, Clause * = NULL);       // Enqueue a literal. Assumes value of literal is undefined.
	Clause * propagate       ();                               // Perform unit propagation. Returns possibly conflicting clause.
	void     cancelUntil     (unsigned);                       // Backtrack until a certain level.
	void     analyze(Clause *, std::vector<Literal> &, int &); // (bt = backtrack)
	void     analyzeFinal(Literal, std::vector<Literal> &);    // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
	bool     litRedundant    (Literal, uint32_t);              // (helper method for 'analyze()')
	Bool     search          (int, int);                       // Search for a given number of conflicts.
	void     reduceDB        ();                               // Reduce the set of learnt clauses.

	// Operations on clauses:
	void attachClause(Clause &);             // Attach a clause to watcher lists.
	void removeClause(Clause &);             // Detach and free a clause.
	bool satisfied(const Clause &) const;    // Returns TRUE if a clause is satisfied in the current state.

	// Misc:
	double progressEstimate()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...

	// Debug:
	void verifyModel();
	void checkLiteralCount();
};

SATSolver::SATSolver(unsigned vars, const std::vector< std::vector<int> > & c)
	: variables(vars)
	, solution(vars, false)

	, watches(2 * vars)
	, reason(vars, 0)
	, level(vars, -1)
	, seen(vars, 0)
	, ok(true)
	, assigns(vars)
	, var_sel(vars)

	, clause_decay(1 / 0.999)
	, restart_first(100)
	, restart_inc(1.5)
	, learntsize_factor((double)1 / (double)3)
	, learntsize_inc(1.1)
	, expensive_ccmin  (true)
	, verbosity        (0)
	, starts(0), decisions(0), propagations(0), conflicts(0)
	, clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
	, cla_inc          (1)
	, qhead            (0)
	, simpDB_assigns   (-1)
	, simpDB_props     (0)
	, progress_estimate(0)
	, remove_satisfied (true)
{
	for(unsigned i = 0; i < c.size(); i++)
	{
		unsigned size = c[i].size();
		std::vector<Literal> lits(size);
		for(unsigned j = 0; j < size; j++)
		{
			int cur = c[i] [j];
			if(cur == 0) throw std::runtime_error("Zero");

			unsigned var = abs(cur) - 1;
			if(var >= variables)
				throw std::runtime_error("Too big");

			lits[j] = (cur > 0) ? Literal(var) : ~Literal(var);
		}
		addClause(lits);
	}
}

SATSolver::~SATSolver()
{
	for(unsigned i = 0; i < learnts.size(); i++)
		free(learnts[i]);

	for(unsigned i = 0; i < clauses.size(); i++)
		free(clauses[i]);
}

bool SATSolver::sat()
{
	if(!ok) return false;
	if(!simplify())
	{
		fprintf(stderr, "Solved by unit propagation\n");
		return false;
	}
	return solve();
}

//=================================================================================================
// Minor methods:

bool SATSolver::addClause(std::vector<Literal> & ps)
{
	assert(decisionLevel() == 0);
	if(!ok) return false;

	std::sort(ps.begin(), ps.end());
	Literal p;
	unsigned i, j;
	for(i = j = 0, p = Literal::UNDEF; i < ps.size(); i++)
		if(assigns[ps[i]] == Bool::TRUE || ps[i] == ~p)
			return true;
		else if(assigns[ps[i]] != Bool::FALSE && ps[i] != p)
			ps[j++] = p = ps[i];
	ps.resize(j);

	if(ps.size() == 0) return ok = false;
	else if(ps.size() == 1)
	{
		assert(assigns[ps[0]] == Bool::UNDEF);
		uncheckedEnqueue(ps[0]);
		return ok = (propagate() == NULL);
	}
	else
	{
		Clause * c = Clause_new(ps, false);
		clauses.push_back(c);
		attachClause(*c);
	}
	return true;
}

void SATSolver::attachClause(Clause & c)
{
	assert(c.size() > 1);
	watches[(~c[0]).offset()].push_back(&c);
	watches[(~c[1]).offset()].push_back(&c);
	if(c.learnt()) learnts_literals += c.size();
	else clauses_literals += c.size();
}

void SATSolver::removeClause(Clause & c)
{
	assert(c.size() > 1);
	assert(find(watches[(~c[0]).offset()], &c));
	assert(find(watches[(~c[1]).offset()], &c));

	remove_vector(watches[(~c[0]).offset()], &c);
	remove_vector(watches[(~c[1]).offset()], &c);

	if(c.learnt()) learnts_literals -= c.size();
	else           clauses_literals -= c.size();

	free(&c);
}

bool SATSolver::satisfied(const Clause & c) const
{
	for(unsigned i = 0; i < c.size(); i++)
		if(assigns[c[i]] == Bool::TRUE)
			return true;
	return false;
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
void SATSolver::cancelUntil(unsigned level)
{
	if(decisionLevel() > level)
	{
		for(int c = (int)trail.size() - 1; c >= trail_lim[level]; c--)
		{
			unsigned x = trail[c].var();
			assigns.set(x, Bool::UNDEF);
			var_sel.insertVarOrder(x);
		}
		qhead = trail_lim[level];
		trail.resize(trail_lim[level]);
		trail_lim.resize(level);
	}
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Literal>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|  
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
void SATSolver::analyze(Clause * confl, std::vector<Literal> & out_learnt, int & out_btlevel)
{
	int pathC = 0;
	Literal p = Literal::UNDEF;

	// Generate conflict clause:
	out_learnt.push_back(Literal(0));      // (leave room for the asserting literal)
	int index = trail.size() - 1;
	out_btlevel = 0;

	do
	{
		assert(confl != NULL);          // (otherwise should be UIP)
		Clause & c = *confl;

		if(c.learnt())
			claBumpActivity(c);

		for(unsigned j = (p == Literal::UNDEF) ? 0 : 1; j < c.size(); j++)
		{
			Literal q = c[j];
			if(!seen[q.var()] && level[q.var()] > 0)
			{
				var_sel.bumpActivity(q.var());
				seen[q.var()] = 1;
				if(level[q.var()] >= (int)decisionLevel())
					pathC++;
				else
				{
					out_learnt.push_back(q);
					if(level[q.var()] > out_btlevel)
						out_btlevel = level[q.var()];
				}
			}
		}

		// Select next clause to look at:
		while(!seen[trail[index--].var()]) {}
		p = trail[index + 1];
		confl = reason[p.var()];
		seen[p.var()] = 0;
		pathC--;
	} while(pathC > 0);
	out_learnt[0] = ~p;

	// Simplify conflict clause:
	unsigned i, j;
	if(expensive_ccmin)
	{
		uint32_t abstract_level = 0;
		for(i = 1; i < out_learnt.size(); i++)
			abstract_level |= abstractLevel(out_learnt[i].var()); // (maintain an abstraction of levels involved in conflict)

		analyze_toclear = out_learnt;
		for(i = j = 1; i < out_learnt.size(); i++)
			if(reason[out_learnt[i].var()] == NULL || !litRedundant(out_learnt[i], abstract_level))
				out_learnt[j++] = out_learnt[i];
	}
	else
	{
		analyze_toclear = out_learnt;
		for(i = j = 1; i < out_learnt.size(); i++)
		{
			Clause & c = *reason[out_learnt[i].var()];
			for(unsigned k = 1; k < c.size(); k++)
				if(!seen[c[k].var()] && level[c[k].var()] > 0)
				{
					out_learnt[j++] = out_learnt[i];
					break;
				}
		}
	}
	max_literals += out_learnt.size();
	out_learnt.resize(out_learnt.size() - (i - j));
	tot_literals += out_learnt.size();

	// Find correct backtrack level:
	if (out_learnt.size() == 1) out_btlevel = 0;
	else
	{
		int max_i = 1;
		for(unsigned i = 2; i < out_learnt.size(); i++)
			if (level[out_learnt[i].var()] > level[out_learnt[max_i].var()])
				max_i = i;
		Literal p = out_learnt[max_i];
		out_learnt[max_i] = out_learnt[1];
		out_learnt[1] = p;
		out_btlevel = level[p.var()];
	}

	for(unsigned j = 0; j < analyze_toclear.size(); j++)
		seen[analyze_toclear[j].var()] = 0;    // ('seen[]' is now cleared)
}

// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool SATSolver::litRedundant(Literal p, uint32_t abstract_levels)
{
	analyze_stack.clear();
	analyze_stack.push_back(p);

	int top = analyze_toclear.size();
	while(analyze_stack.size() > 0)
	{
		assert(reason[analyze_stack[analyze_stack.size() - 1].var()] != NULL);
		Clause & c = *reason[analyze_stack[analyze_stack.size() - 1].var()];
		analyze_stack.pop_back();
		
		for(unsigned i = 1; i < c.size(); i++)
		{
			Literal p = c[i];
			if(!seen[p.var()] && level[p.var()] > 0)
			{
				if(reason[p.var()] != NULL && (abstractLevel(p.var()) & abstract_levels) != 0)
				{
					seen[p.var()] = 1;
					analyze_stack.push_back(p);
					analyze_toclear.push_back(p);
				}
				else
				{
					for(unsigned j = top; j < analyze_toclear.size(); j++)
						seen[analyze_toclear[j].var()] = 0;
					analyze_toclear.resize(top);
					return false;
				}
			}
		}
	}

	return true;
}

/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Literal)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void SATSolver::analyzeFinal(Literal p, std::vector<Literal> & out_conflict)
{
	out_conflict.clear();
	out_conflict.push_back(p);

	if(decisionLevel() == 0)
		return;

	seen[p.var()] = 1;
	for(int i = trail.size() - 1; i >= trail_lim[0]; i--)
	{
		unsigned x = trail[i].var();
		if(seen[x])
		{
			if (reason[x] == NULL)
			{
				assert(level[x] > 0);
				out_conflict.push_back(~trail[i]);
			}
			else
			{
				Clause& c = *reason[x];
	     			for(unsigned j = 1; j < c.size(); j++)
					if(level[c[j].var()] > 0)
						seen[c[j].var()] = 1;
			}
			seen[x] = 0;
		}
	}
	seen[p.var()] = 0;
}

void SATSolver::uncheckedEnqueue(Literal p, Clause* from)
{
	assert(assigns[p] == Bool::UNDEF);
	assigns.set(p.var(), Bool(!p.sign()));  // <<== abstract but not uttermost effecient
	level[p.var()] = decisionLevel();
	reason[p.var()] = from;
	trail.push_back(p);
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
Clause * SATSolver::propagate()
{
	Clause * confl = NULL;
	int num_props = 0;

	while(qhead < (int)trail.size())
	{
		Literal p = trail[qhead++];     // 'p' is enqueued fact to propagate.
		std::vector<Clause *> & ws = watches[p.offset()];
		num_props++;

		//Clause **i, **j, **end;
		unsigned i, j, end = ws.size();
		for(i = j = 0; i < end; )
		{
			Clause & c = *ws[i++];

			// Make sure the false literal is data[1]:
			Literal false_lit = ~p;
			if(c[0] == false_lit)
				c[0] = c[1], c[1] = false_lit;

			assert(c[1] == false_lit);

			// If 0th watch is true, then clause is already satisfied.
			Literal first = c[0];
			if(assigns[first] == Bool::TRUE)
				ws[j++] = &c;
			else
			{
				// Look for new watch:
				for(unsigned k = 2; k < c.size(); k++)
					if(assigns[c[k]] != Bool::FALSE)
					{
						c[1] = c[k];
						c[k] = false_lit;
						watches[(~c[1]).offset()].push_back(&c);
						goto FoundWatch;
					}

				// Did not find watch -- clause is unit under assignment:
				ws[j++] = &c;
				if(assigns[first] == Bool::FALSE)
				{
					confl = &c;
					qhead = trail.size();
					// Copy the remaining watches:
					while(i < end) ws[j++] = ws[i++];
				}
				else uncheckedEnqueue(first, &c);
			}
	FoundWatch:;
		}
		ws.resize(j);
	}
	propagations += num_props;
	simpDB_props -= num_props;

	return confl;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/

inline bool lessClause(Clause * x, Clause * y)
{
	return x->size() > 2 && (y->size() == 2 || x->activity() < y->activity());
}

void SATSolver::reduceDB()
{
	double extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

	std::sort(learnts.begin(), learnts.end(), lessClause);

	unsigned i, j;
	for(i = j = 0; i < learnts.size() >> 1; i++)
	{
		if (learnts[i]->size() > 2 && !locked(*learnts[i]))
			removeClause(*learnts[i]);
		else learnts[j++] = learnts[i];
	}
	for( ; i < learnts.size(); i++)
	{
		if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() < extra_lim)
			removeClause(*learnts[i]);
		else learnts[j++] = learnts[i];
	}
	learnts.resize(j);
}

void SATSolver::removeSatisfied(std::vector<Clause *> & cs)
{
	unsigned i, j;
	for(i = j = 0; i < cs.size(); i++)
	{
		if(satisfied(*cs[i])) removeClause(*cs[i]);
		else cs[j++] = cs[i];
	}
	cs.resize(j);
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool SATSolver::simplify()
{
	assert(decisionLevel() == 0);

	if(!ok || propagate() != NULL)
		return ok = false;

	if((int)nAssigns() == simpDB_assigns || (simpDB_props > 0))
		return true;

	// Remove satisfied clauses:
	removeSatisfied(learnts);
	if(remove_satisfied)        // Can be turned off.
		removeSatisfied(clauses);

	// Remove fixed variables from the variable heap:
	var_sel.filter(assigns);

	simpDB_assigns = nAssigns();
	simpDB_props = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)
	return true;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [Bool]
|  
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|  
|  Output:
|    'Bool::TRUE' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'Bool::FALSE'
|    if the clause set is unsatisfiable. 'Bool::UNDEF' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
Bool SATSolver::search(int nof_conflicts, int nof_learnts)
{
	assert(ok);
	int backtrack_level;
	int conflictC = 0;
	std::vector<Literal> learnt_clause;

	starts++;

	bool first = true;

	for(;;)
	{
		Clause * confl = propagate();
		if(confl != NULL)
		{
			// CONFLICT
			conflicts++;
			conflictC++;
			if(decisionLevel() == 0) return Bool::FALSE;
			
			first = false;
			
			learnt_clause.clear();
			analyze(confl, learnt_clause, backtrack_level);
			cancelUntil(backtrack_level);
			assert(assigns[learnt_clause[0]] == Bool::UNDEF);
			
			if(learnt_clause.size() == 1)
				uncheckedEnqueue(learnt_clause[0]);
			else
			{
				Clause * c = Clause_new(learnt_clause, true);
				learnts.push_back(c);
				attachClause(*c);
				claBumpActivity(*c);
				uncheckedEnqueue(learnt_clause[0], c);
			}
			
			var_sel.decayActivity();
			claDecayActivity();
		}
		else
		{
			// NO CONFLICT
			if(nof_conflicts >= 0 && conflictC >= nof_conflicts)
			{
				// Reached bound on number of conflicts:
				progress_estimate = progressEstimate();
				cancelUntil(0);
				return Bool::UNDEF;
			}

			// Simplify the set of problem clauses:
			if(decisionLevel() == 0 && !simplify())
				return Bool::FALSE;
			
			if(nof_learnts >= 0 && (int)(learnts.size() - nAssigns()) >= nof_learnts)
				// Reduce the set of learnt clauses:
				reduceDB();

			Literal next = Literal::UNDEF;
			while(decisionLevel() < assumptions.size())
			{
				// Perform user provided assumption:
				Literal p = assumptions[decisionLevel()];
				if(assigns[p] == Bool::TRUE)
				{
					// Dummy decision level:
					newDecisionLevel();
				}
				else if(assigns[p] == Bool::FALSE)
				{
					analyzeFinal(~p, conflict);
					return Bool::FALSE;
				}
				else
				{
					next = p;
					break;
				}
			}

			if(next == Literal::UNDEF)
			{
				// New variable decision:
				decisions++;
				next = var_sel.getBranchLiteral(assigns);

				if(next == Literal::UNDEF) // Model found:
					return Bool::TRUE;
			}

			// Increase decision level and enqueue 'next'
			assert(assigns[next] == Bool::UNDEF);
			newDecisionLevel();
			uncheckedEnqueue(next);
		}
	}
}

double SATSolver::progressEstimate() const
{
	double progress = 0;
	double F = 1.0 / variables;

	for(unsigned i = 0; i <= decisionLevel(); i++)
	{
		int beg = i == 0 ? 0 : trail_lim[i - 1];
		int end = i == decisionLevel() ? trail.size() : trail_lim[i];
		progress += pow(F, i) * (end - beg);
	}
	return progress / variables;
}

bool SATSolver::solve(const std::vector<Literal> & assumps)
{
	model.clear();
	conflict.clear();

	if(!ok) return false;

	assumptions = assumps;

	double nof_conflicts = restart_first;
	double nof_learnts = nClauses() * learntsize_factor;
	Bool status = Bool::UNDEF;

	if(verbosity >= 1)
	{
		printf("============================[ Search Statistics ]==============================\n");
		printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
		printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
		printf("===============================================================================\n");
	}

	// Search:
	while(status == Bool::UNDEF)
	{
		if(verbosity >= 1)
			printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", (int)conflicts, var_sel.size(), nClauses(), (int)clauses_literals, (int)nof_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progress_estimate*100), fflush(stdout);
		status = search((int)nof_conflicts, (int)nof_learnts);
		nof_conflicts *= restart_inc;
		nof_learnts *= learntsize_inc;
	}

	if(verbosity >= 1)
		printf("===============================================================================\n");

	if(status == Bool::TRUE)
	{
		// Extend & copy model:
		model.resize(variables);
		for(unsigned i = 0; i < variables; i++)
			model[i] = assigns[i];
		verifyModel();
	}
	else
	{
		assert(status == Bool::FALSE);
		if(conflict.size() == 0)
			ok = false;
	}

	cancelUntil(0);
	return status == Bool::TRUE;
}

//=================================================================================================
// Debug methods:

void SATSolver::verifyModel()
{
	bool failed = false;
	for(unsigned i = 0; i < clauses.size(); i++)
	{
		assert(clauses[i]->mark() == 0);
		Clause & c = *clauses[i];
		for(unsigned j = 0; j < c.size(); j++)
			if(modelValue(c[j]) == Bool::TRUE)
				goto next;

		printf("unsatisfied clause: %s\n", clauses[i]->toString().c_str());
		failed = true;
next:;
	}

	assert(!failed);
	printf("Verified %u original clauses.\n", clauses.size());
}


void SATSolver::checkLiteralCount()
{
	int cnt = 0;
	for(unsigned i = 0; i < clauses.size(); i++)
		if (clauses[i]->mark() == 0)
			cnt += clauses[i]->size();

	if((int)clauses_literals != cnt)
	{
		fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
		assert((int)clauses_literals == cnt);
	}
}








int main(int argn, char * args[])
{
	if(argn != 2)
	{
		fprintf(stderr, "Incorrect command line\n");
		return 0;
	}

	freopen(args[1], "r", stdin);

	minisat::Solver S;
	S.verbosity = 1;

	int n, m;
	scanf("p cnf %i %i", &n, &m);

	std::vector< std::vector<int> > clauses(m);
	for(int i = 0; i < m; i++)
	{
		minisat::vec<minisat::Lit> lits;
		std::vector<int> clause;

		while(1)
		{
			int cur;
			scanf("%i", &cur);
			if(cur == 0) break;

			clause.push_back(cur);

			int var = abs(cur) - 1;
		        while(var >= S.nVars()) S.newVar();
			lits.push( (cur > 0) ? minisat::Lit(var) : ~minisat::Lit(var) );
		}
		S.addClause(lits);
		clauses[i] = clause;
	}

	SATSolver solver(n, clauses);
	solver.verbosity = 1;

	double mstime = clock();
	bool msres;
	if(!S.simplify())
	{
		fprintf(stderr, "Solved by unit propagation\n");
		msres = false;
	}
	else msres = S.solve();
	mstime = (clock() - mstime) / CLOCKS_PER_SEC;

	fprintf(stderr, msres ? "SAT\n" : "UNSAT\n");
	fprintf(stderr, "%lf sec\n", mstime);


	double mytime = clock();
	bool myres = solver.sat();
	mytime = (clock() - mytime) / CLOCKS_PER_SEC;

	fprintf(stderr, myres ? "SAT\n" : "UNSAT\n");
	fprintf(stderr, "%lf sec\n", mytime);

	bool ok = true;
	if((unsigned)S.nVars() != solver.variables) ok = false;
	else
	{
		//for(int i = 0; i < S.nVars(); i++)
		//	if(!(S.model[i] == solver.model[i]))
		//		ok = false;
	}

	fprintf(stderr, ok ? "Solutions are ok\n" : "ERROR\n");

	return 0;
}
