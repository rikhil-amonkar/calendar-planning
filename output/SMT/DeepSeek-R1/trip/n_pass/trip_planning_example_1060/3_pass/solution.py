from z3 import *

def main():
    cities = {
        0: 'Reykjavik',
        1: 'Stuttgart',
        2: 'Istanbul',
        3: 'Vilnius',
        4: 'Seville',
        5: 'Geneva',
        6: 'Valencia',
        7: 'Munich'
    }
    
    flights = [
        (0, 7), (7, 0),
        (0, 1),
        (1, 6), (6, 1),
        (1, 2), (2, 1),
        (7, 5), (5, 7),
        (2, 3), (3, 2),
        (6, 4), (4, 6),
        (6, 2), (2, 6),
        (3, 7),
        (4, 7), (7, 4),
        (7, 2), (2, 7),
        (6, 5), (5, 6),
        (6, 7), (7, 6),
        (5, 2), (2, 5)
    ]
    
    s = Solver()
    
    c = [Int(f'c_{i}') for i in range(25)]
    
    for i in range(25):
        s.add(And(c[i] >= 0, c[i] <= 7))
    
    s.add(c[0] == 0)
    s.add(c[1] == 0)
    s.add(c[2] == 0)
    s.add(c[3] == 1)
    s.add(c[4] == 1)
    s.add(c[5] == 1)
    s.add(c[6] == 1)
    s.add(c[12] == 7)
    s.add(c[13] == 7)
    s.add(c[14] == 7)
    s.add(c[18] == 2)
    s.add(c[19] == 2)
    s.add(c[20] == 2)
    s.add(c[21] == 2)
    
    for i in range(1, 25):
        prev = c[i-1]
        curr = c[i]
        flight_taken = (prev != curr)
        allowed_flight = Or([And(prev == f, curr == t) for (f, t) in flights])
        s.add(If(flight_taken, allowed_flight, True))
    
    total_days = [0]*8
    for j in range(8):
        count_j = 0
        for i in range(25):
            if i == 0:
                count_j += If(c[i] == j, 1, 0)
            else:
                cond = c[i-1] != c[i]
                count_j += If(cond, 
                              If(Or(c[i-1] == j, c[i] == j), 1, 0),
                              If(c[i] == j, 1, 0))
        s.add(count_j == [4, 4, 4, 4, 3, 5, 5, 3][j])
    
    if s.check() == sat:
        m = s.model()
        seq = [m.evaluate(c[i]).as_long() for i in range(25)]
        itinerary = []
        for day in range(25):
            if day == 0:
                cities_today = [cities[seq[0]]]
            else:
                if seq[day] == seq[day-1]:
                    cities_today = [cities[seq[day]]]
                else:
                    cities_today = [cities[seq[day-1]], cities[seq[day]]]
            itinerary.append((day+1, cities_today))
        
        for day, cities_list in itinerary:
            print(f"Day {day}: {', '.join(cities_list)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()