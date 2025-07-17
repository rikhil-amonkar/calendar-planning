from z3 import *

def main():
    cities = ["Geneva", "Munich", "Bucharest", "Valencia", "Stuttgart"]
    s = Solver()
    
    seq = [Int('seq0'), Int('seq1'), Int('seq2'), Int('seq3'), Int('seq4')]
    start = [Int(f'start_{i}') for i in range(5)]
    end = [Int(f'end_{i}') for i in range(5)]
    
    s.add(Distinct(seq))
    for i in range(5):
        s.add(seq[i] >= 0, seq[i] < 5)
    
    s.add(seq[0] == 0)  # First city is Geneva
    s.add(seq[1] == 1)  # Second city is Munich
    
    s.add(start[0] == 1)
    s.add(end[0] == 4)  # Geneva: 1 to 4 (4 days)
    s.add(start[1] == 4)
    s.add(end[1] == 10)  # Munich: 4 to 10 (7 days)
    
    s.add(end[2] == start[2] + 1)  # Bucharest: 2 days
    s.add(end[3] == start[3] + 5)  # Valencia: 6 days
    s.add(end[4] == start[4] + 1)  # Stuttgart: 2 days
    
    def get_start(city):
        return If(city == 0, start[0],
              If(city == 1, start[1],
              If(city == 2, start[2],
              If(city == 3, start[3],
                 start[4]))))
    
    def get_end(city):
        return If(city == 0, end[0],
              If(city == 1, end[1],
              If(city == 2, end[2],
              If(city == 3, end[3],
                 end[4]))))
    
    for j in range(4):
        s.add(get_end(seq[j]) == get_start(seq[j+1]))
    
    s.add(get_end(seq[4]) == 17)
    
    allowed_pairs = [
        (0,1), (1,0),
        (0,3), (3,0),
        (1,2), (2,1),
        (1,3), (3,1),
        (2,3), (3,2),
        (3,4), (4,3)
    ]
    
    for j in range(4):
        c1 = seq[j]
        c2 = seq[j+1]
        s.add(Or([And(c1 == a, c2 == b) for (a, b) in allowed_pairs]))
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(5)]
        start_val = [m.evaluate(start[i]).as_long() for i in range(5)]
        end_val = [m.evaluate(end[i]).as_long() for i in range(5)]
        
        itinerary = []
        for i in range(5):
            city_idx = seq_val[i]
            city_name = cities[city_idx]
            s_day = start_val[city_idx]
            e_day = end_val[city_idx]
            
            if s_day == e_day:
                day_str = f"Day {s_day}"
            else:
                day_str = f"Day {s_day}-{e_day}"
            itinerary.append({"day_range": day_str, "place": city_name})
            
            if i < 4:
                itinerary.append({"day_range": f"Day {e_day}", "place": city_name})
                next_city_idx = seq_val[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({"day_range": f"Day {e_day}", "place": next_city_name})
        
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()