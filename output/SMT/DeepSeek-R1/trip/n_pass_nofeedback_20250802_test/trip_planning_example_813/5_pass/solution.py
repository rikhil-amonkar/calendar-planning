import z3

def main():
    s = z3.Solver()
    cities_list = ['Vilnius', 'Frankfurt', 'Stuttgart', 'London', 'Santorini', 'Dublin', 'Seville']
    
    d = [z3.Int(f'd_{i}') for i in range(7)]
    city = [z3.Int(f'city_{i}') for i in range(7)]
    
    for i in range(7):
        s.add(d[i] >= 2)
    s.add(sum(d) == 17)
    
    for i in range(7):
        s.add(city[i] >= 0, city[i] <= 6)
    s.add(z3.Distinct(city))
    
    s.add(city[0] == 0)
    s.add(city[6] == 6)
    
    if s.check() == z3.sat:
        m = s.model()
        d_vals = [m.eval(d_i).as_long() for d_i in d]
        city_vals = [m.eval(city_i).as_long() for city_i in city]
        
        starts = [1]
        for i in range(1, 7):
            starts.append(starts[i-1] + d_vals[i-1])
        
        itinerary = []
        for i in range(7):
            start_day = starts[i]
            end_day = starts[i] + d_vals[i] - 1
            day_range = f"Day {start_day}-{end_day}"
            place = cities_list[city_vals[i]]
            itinerary.append({'day_range': day_range, 'place': place})
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()