from z3 import *

def main():
    cities = ["Madrid", "Dublin", "Tallinn"]
    n_days = 7
    c = [Int('c_%d' % i) for i in range(n_days)]
    s = Solver()
    
    # Each day must be 0, 1, or 2
    for i in range(n_days):
        s.add(And(c[i] >= 0, c[i] <= 2))
    
    # Start in Madrid, end in Tallinn, visit Dublin at least once
    s.add(c[0] == 0)
    s.add(c[6] == 2)
    s.add(Or([c[i] == 1 for i in range(n_days)]))
    
    # Adjacency constraint
    for i in range(n_days - 1):
        s.add(Abs(c[i] - c[i+1]) <= 1)
    
    # No three distinct cities in any three consecutive days
    for i in range(n_days - 2):
        s.add(Or(c[i] == c[i+1], c[i] == c[i+2], c[i+1] == c[i+2]))
    
    if s.check() == sat:
        model = s.model()
        city_list = [model.evaluate(c[i]).as_long() for i in range(n_days)]
        city_names = [cities[idx] for idx in city_list]
        
        itinerary = []
        i = 0
        while i < n_days:
            j = i
            current_city = city_names[i]
            while j < n_days and city_names[j] == current_city:
                j += 1
            start_day = i + 1
            end_day = j
            day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
            itinerary.append({'day_range': day_range, 'place': current_city})
            i = j
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()