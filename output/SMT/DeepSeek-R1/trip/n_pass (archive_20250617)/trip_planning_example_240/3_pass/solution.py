from z3 import *

def main():
    City, (Prague, Berlin, Tallinn, Stockholm) = EnumSort('City', ['Prague', 'Berlin', 'Tallinn', 'Stockholm'])
    
    allowed_pairs = [
        (Berlin, Tallinn),
        (Tallinn, Berlin),
        (Prague, Tallinn),
        (Tallinn, Prague),
        (Stockholm, Tallinn),
        (Tallinn, Stockholm),
        (Prague, Stockholm),
        (Stockholm, Prague),
        (Stockholm, Berlin),
        (Berlin, Stockholm)
    ]
    
    L = [ Const(f'L_{i}', City) for i in range(13) ]
    
    s = Solver()
    
    # Start in Prague (L0)
    s.add(L[0] == Prague)
    
    for d in range(12):
        stay = (L[d] == L[d+1])
        travel = Or([And(L[d] == c1, L[d+1] == c2) for (c1, c2) in allowed_pairs])
        s.add(Or(stay, travel))
    
    total_Prague = 0
    total_Berlin = 0
    total_Tallinn = 0
    total_Stockholm = 0
    
    for d in range(12):
        total_Prague += If(Or(L[d] == Prague, L[d+1] == Prague), 1, 0)
        total_Berlin += If(Or(L[d] == Berlin, L[d+1] == Berlin), 1, 0)
        total_Tallinn += If(Or(L[d] == Tallinn, L[d+1] == Tallinn), 1, 0)
        total_Stockholm += If(Or(L[d] == Stockholm, L[d+1] == Stockholm), 1, 0)
    
    s.add(total_Prague == 2)
    s.add(total_Berlin == 3)
    s.add(total_Tallinn == 5)
    s.add(total_Stockholm == 5)
    
    # Conference in Berlin on day 6 and 8
    s.add(Or(L[5] == Berlin, L[6] == Berlin))  # Day 6
    s.add(Or(L[7] == Berlin, L[8] == Berlin))  # Day 8
    
    # In Tallinn from day 8 to 12 inclusive
    s.add(Or(L[7] == Tallinn, L[8] == Tallinn))  # Day 8
    s.add(Or(L[8] == Tallinn, L[9] == Tallinn))  # Day 9
    s.add(Or(L[9] == Tallinn, L[10] == Tallinn)) # Day 10
    s.add(Or(L[10] == Tallinn, L[11] == Tallinn))# Day 11
    s.add(Or(L[11] == Tallinn, L[12] == Tallinn))# Day 12
    
    if s.check() == sat:
        m = s.model()
        locs = [m.evaluate(L[i]) for i in range(13)]
        city_names = {Prague: 'Prague', Berlin: 'Berlin', Tallinn: 'Tallinn', Stockholm: 'Stockholm'}
        
        for day in range(12):
            start = locs[day]
            end = locs[day+1]
            if start == end:
                print(f"Day {day+1}: in {city_names[start]}")
            else:
                cities = sorted([city_names[start], city_names[end]])
                print(f"Day {day+1}: in {cities[0]} and {cities[1]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()