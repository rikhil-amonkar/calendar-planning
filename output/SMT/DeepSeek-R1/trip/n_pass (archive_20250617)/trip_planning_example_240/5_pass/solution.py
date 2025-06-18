from z3 import *

def main():
    City, (Prague, Berlin, Tallinn, Stockholm) = EnumSort('City', ['Prague', 'Berlin', 'Tallinn', 'Stockholm'])
    
    # Reordered to prioritize Prague-Stockholm flight
    allowed_pairs = [
        (Prague, Stockholm),
        (Stockholm, Prague),
        (Berlin, Tallinn),
        (Tallinn, Berlin),
        (Prague, Tallinn),
        (Tallinn, Prague),
        (Stockholm, Tallinn),
        (Tallinn, Stockholm),
        (Stockholm, Berlin),
        (Berlin, Stockholm)
    ]
    
    L = [ Const(f'L_{i}', City) for i in range(13) ]
    
    s = Solver()
    
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
    
    s.add(Or(L[5] == Berlin, L[6] == Berlin))
    s.add(Or(L[7] == Berlin, L[8] == Berlin))
    
    for day in [8, 9, 10, 11, 12]:
        s.add(Or(L[day-1] == Tallinn, L[day] == Tallinn))
    
    if s.check() == sat:
        m = s.model()
        locs = [m.evaluate(L[i]) for i in range(13)]
        city_names = {Prague: 'Prague', Berlin: 'Berlin', Tallinn: 'Tallinn', Stockholm: 'Stockholm'}
        
        for day in range(1, 13):
            start = locs[day-1]
            end = locs[day]
            if start == end:
                print(f"Day {day}: in {city_names[start]}")
            else:
                cities = sorted([city_names[start], city_names[end]], key=lambda x: x)
                print(f"Day {day}: in {cities[0]} and {cities[1]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()