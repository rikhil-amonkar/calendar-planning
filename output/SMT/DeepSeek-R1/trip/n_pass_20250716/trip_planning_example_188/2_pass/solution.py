from z3 import *

def main():
    City = Datatype('City')
    City.declare('Brussels')
    City.declare('Barcelona')
    City.declare('Split')
    City = City.create()
    
    base_city = [ Const('base_city_%d' % i, City) for i in range(1, 14) ]
    travel = [ Bool('travel_%d' % i) for i in range(1, 13) ]
    
    s = Solver()
    
    s.add(base_city[0] == City.Brussels)
    
    def adjacent(c1, c2):
        return Or(
            And(c1 == City.Brussels, c2 == City.Barcelona),
            And(c1 == City.Barcelona, c2 == City.Brussels),
            And(c1 == City.Barcelona, c2 == City.Split),
            And(c1 == City.Split, c2 == City.Barcelona)
        )
    
    for i in range(0, 12):
        s.add(
            If(travel[i],
               And(base_city[i] != base_city[i+1], adjacent(base_city[i], base_city[i+1])),
               base_city[i+1] == base_city[i]
            )
        )
    
    in_Brussels = [ Or(base_city[i] == City.Brussels, 
                    And(travel[i], base_city[i+1] == City.Brussels)) 
                  for i in range(0, 12) ]
    in_Barcelona = [ Or(base_city[i] == City.Barcelona, 
                     And(travel[i], base_city[i+1] == City.Barcelona)) 
                   for i in range(0, 12) ]
    in_Split = [ Or(base_city[i] == City.Split, 
                 And(travel[i], base_city[i+1] == City.Split)) 
               for i in range(0, 12) ]
    
    s.add(Sum([If(cond, 1, 0) for cond in in_Brussels]) == 2)
    s.add(Sum([If(cond, 1, 0) for cond in in_Barcelona]) == 7)
    s.add(Sum([If(cond, 1, 0) for cond in in_Split]) == 5)
    
    s.add(Sum([If(travel[i], 1, 0) for i in range(0,12)]) == 2)
    
    s.add(in_Brussels[0] == True)
    s.add(in_Brussels[1] == True)
    
    if s.check() == sat:
        m = s.model()
        base_city_vals = [m[base_city[i]] for i in range(0, 13)]
        travel_vals = [m[travel[i]] for i in range(0, 12)]
        
        city_names = { 
            City.Brussels: "Brussels", 
            City.Barcelona: "Barcelona", 
            City.Split: "Split" 
        }
        base_city_str = [city_names[base_city_vals[i]] for i in range(0, 13)]
        travel_bool = [is_true(travel_vals[i]) for i in range(0, 12)]
        
        travel_days = [day for day in range(1, 13) if travel_bool[day-1]]
        
        segments = []
        start = 1
        current_city = base_city_str[0]
        for day in range(1, 13):
            if day in travel_days:
                if start < day:
                    segments.append((start, day-1, current_city))
                segments.append((day, day, current_city))
                current_city = base_city_str[day]
                start = day + 1
            else:
                if day == 12:
                    segments.append((start, 12, current_city))
                else:
                    next_city = base_city_str[day]
                    if next_city != current_city:
                        if start < day:
                            segments.append((start, day-1, current_city))
                        segments.append((day, day, current_city))
                        current_city = next_city
                        start = day + 1
                    else:
                        if day == 12:
                            segments.append((start, 12, current_city))
        if start <= 12:
            segments.append((start, 12, current_city))
        
        itinerary = []
        for (s, e, city) in segments:
            if s == e:
                day_range = f"Day {s}"
            else:
                day_range = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range, "place": city})
        
        for day in travel_days:
            from_city = base_city_str[day-1]
            to_city = base_city_str[day]
            itinerary.append({"day_range": f"Day {day}", "place": from_city})
            itinerary.append({"day_range": f"Day {day}", "place": to_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()