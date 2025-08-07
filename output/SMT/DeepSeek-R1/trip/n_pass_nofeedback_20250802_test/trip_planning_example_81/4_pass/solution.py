import z3

def main():
    s = z3.Solver()
    city = [z3.Int('city%d' % i) for i in range(10)]
    
    for i in range(10):
        s.add(z3.Or(city[i] == 0, city[i] == 1, city[i] == 2))
    
    allowed_transitions = [
        (0, 1), (1, 0),
        (1, 2), (2, 1)
    ]
    for i in range(1, 10):
        prev = city[i-1]
        curr = city[i]
        s.add(z3.Or(
            prev == curr,
            z3.Or([z3.And(prev == a, curr == b) for (a, b) in allowed_transitions])
        ))
    
    s.add(z3.Or(city[3] == 0, city[4] == 0))
    s.add(z3.Or(city[8] == 0, city[9] == 0))
    
    total_myk = 0
    total_bud = 0
    total_ham = 0
    for i in range(1, 10):
        start_myk = z3.If(city[i-1] == 0, 1, 0)
        end_myk = z3.If(z3.And(city[i] == 0, city[i-1] != 0), 1, 0)
        total_myk += (start_myk + end_myk)
        
        start_bud = z3.If(city[i-1] == 1, 1, 0)
        end_bud = z3.If(z3.And(city[i] == 1, city[i-1] != 1), 1, 0)
        total_bud += (start_bud + end_bud)
        
        start_ham = z3.If(city[i-1] == 2, 1, 0)
        end_ham = z3.If(z3.And(city[i] == 2, city[i-1] != 2), 1, 0)
        total_ham += (start_ham + end_ham)
    
    s.add(total_myk == 6)
    s.add(total_bud == 3)
    s.add(total_ham == 2)
    
    if s.check() == z3.sat:
        model = s.model()
        city_names = {0: "Mykonos", 1: "Budapest", 2: "Hamburg"}
        end_cities = [model.eval(city[i]).as_long() for i in range(1, 10)]
        
        itinerary = []
        current_place = end_cities[0]
        start_day = 1
        current_end_day = 1
        for day_index in range(1, 9):
            if end_cities[day_index] == current_place:
                current_end_day = day_index + 1
            else:
                if start_day == current_end_day:
                    day_range_str = "Day %d" % start_day
                else:
                    day_range_str = "Day %d-%d" % (start_day, current_end_day)
                itinerary.append({'day_range': day_range_str, 'place': city_names[current_place]})
                current_place = end_cities[day_index]
                start_day = day_index + 1
                current_end_day = start_day
        
        if start_day == 9:
            day_range_str = "Day 9"
        else:
            day_range_str = "Day %d-%d" % (start_day, 9)
        itinerary.append({'day_range': day_range_str, 'place': city_names[current_place]})
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()