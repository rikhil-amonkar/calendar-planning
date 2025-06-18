from z3 import *

def main():
    s = Solver()
    days = 17
    n = [Bool(f'n_{i}') for i in range(1, days+1)]
    vn = [Bool(f'vn_{i}') for i in range(1, days+1)]
    vl = [Bool(f'vl_{i}') for i in range(1, days+1)]
    
    for i in range(days):
        s.add(Or(n[i], vn[i], vl[i]))
        s.add(Not(And(n[i], vl[i])))
        s.add(Not(And(n[i], vn[i], vl[i])))
    
    # Naples: 5 consecutive days (days 1-5)
    for i in range(5):
        s.add(n[i])
    for i in range(5, days):
        s.add(Not(n[i]))
    
    # Vienna: 7 days total
    s.add(sum([If(vn[i], 1, 0) for i in range(days)]) == 7)
    # Vilnius: 7 days total
    s.add(sum([If(vl[i], 1, 0) for i in range(days)]) == 7)
    
    # Travel from Naples to Vienna on day 5 (index 4)
    s.add(vn[4])
    # Travel from Vienna to Vilnius on day 11 (index 10)
    s.add(vn[10], vl[10])
    
    # Continuity between consecutive days
    for i in range(days-1):
        s.add(Or(
            And(n[i], n[i+1]),
            And(vn[i], vn[i+1]),
            And(vl[i], vl[i+1])
        ))
    
    if s.check() == sat:
        m = s.model()
        for i in range(days):
            in_n = m.evaluate(n[i])
            in_vn = m.evaluate(vn[i])
            in_vl = m.evaluate(vl[i])
            
            if in_n and not in_vn and not in_vl:
                print(f"Day {i+1}: Naples")
            elif not in_n and in_vn and not in_vl:
                print(f"Day {i+1}: Vienna")
            elif not in_n and not in_vn and in_vl:
                print(f"Day {i+1}: Vilnius")
            elif in_n and in_vn and not in_vl:
                print(f"Day {i+1}: Travel between Naples and Vienna")
            elif not in_n and in_vn and in_vl:
                print(f"Day {i+1}: Travel between Vienna and Vilnius")
            else:
                print(f"Day {i+1}: Unexpected state")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()