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
    
    n = 5  # We must visit exactly 5 distinct cities
    s = Solver()
    
    # Create Z3 variables
    city_vars = [Int(f'city_{i}') for i in range(n)]
    start_vars = [Int(f'start_{i}') for i in range(n)]
    end_vars = [Int(f'end_{i}') for i in range(n)]
    duration_vars = [Int(f'duration_{i}') for i in range(n)]
    
    # Create travel time matrix as Z3 array
    tt_arr = Array('tt_arr', IntSort(), IntSort())
    idx = 0
    for i in range(6):
        for j in range(6):
            tt_arr = Store(tt_arr, idx, tt_matrix[i][j])
            idx += 1
    
    # Basic constraints for each stay
    for i in range(n):
        s.add(duration_vars[i] >= 1, duration_vars[i] <= 4)
        s.add(end_vars[i] == start_vars[i] + duration_vars[i] - 1)
        s.add(start_vars[i] >= 1, end_vars[i] <= 13)
        s.add(city_vars[i] >= 0, city_vars[i] <= 5)
    
    # Distinct cities
    s.add(Distinct(city_vars))
    
    # Trip boundaries
    s.add(start_vars[0] == 1)
    s.add(end_vars[n-1] == 13)
    
    # Travel time constraints
    for i in range(n-1):
        c1 = city_vars[i]
        c2 = city_vars[i+1]
        index = c1 * 6 + c2  # Calculate flattened index
        travel_time = Select(tt_arr, index)
        s.add(start_vars[i+1] == end_vars[i] + 1 + travel_time)
    
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
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()