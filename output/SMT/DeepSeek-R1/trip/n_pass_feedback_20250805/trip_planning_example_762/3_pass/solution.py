from z3 import *

def main():
    cities = ['London', 'Madrid', 'Berlin', 'Dublin', 'Oslo', 'Vilnius']
    tt_matrix = [
        [0, 1, 2, 1, 2, 3],
        [1, 0, 2, 2, 3, 4],
        [2, 2, 0, 2, 2, 1],
        [1, 2, 2, 0, 2, 3],
        [2, 3, 2, 2, 0, 2],
        [3, 4, 1, 3, 2, 0]
    ]
    
    for n in [5, 4, 3]:
        s = Solver()
        city_vars = [Int(f'city_{i}') for i in range(n)]
        start_vars = [Int(f'start_{i}') for i in range(n)]
        end_vars = [Int(f'end_{i}') for i in range(n)]
        duration_vars = [Int(f'duration_{i}') for i in range(n)]
        
        for i in range(n):
            s.add(duration_vars[i] >= 1, duration_vars[i] <= 4)
            s.add(end_vars[i] == start_vars[i] + duration_vars[i] - 1)
            s.add(start_vars[i] >= 1, end_vars[i] <= 13)
        
        s.add(Distinct(city_vars))
        for i in range(n):
            s.add(city_vars[i] >= 0, city_vars[i] <= 5)
        
        s.add(start_vars[0] == 1)
        s.add(end_vars[n-1] == 13)
        
        for i in range(n-1):
            T_i = Int(f'T_{i}')
            cases = []
            for c1 in range(6):
                for c2 in range(6):
                    cases.append(And(city_vars[i] == c1, city_vars[i+1] == c2, T_i == tt_matrix[c1][c2]))
            s.add(Or(cases))
            s.add(start_vars[i+1] == end_vars[i] + 1 + T_i)
        
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for i in range(n):
                c_val = m.eval(city_vars[i]).as_long()
                start_val = m.eval(start_vars[i]).as_long()
                end_val = m.eval(end_vars[i]).as_long()
                city_name = cities[c_val]
                day_range = f"Day {start_val}-{end_val}" if start_val != end_val else f"Day {start_val}"
                itinerary.append({'day_range': day_range, 'place': city_name})
            print({'itinerary': itinerary})
            return
        
    print("No valid plan found for n=3,4,5")

if __name__ == '__main__':
    main()