from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Cities: London=0, Santorini=1, Split=2
    cities = ["London", "Santorini", "Split"]
    
    # Variables for each day's starting city (day 1 to 18)
    city = [Int(f'city_{i}') for i in range(1, 19)]
    for c in city:
        s.add(Or(c == 0, c == 1, c == 2))
    
    # Flight variables for days 1 to 17
    fly = [Bool(f'fly_{i}') for i in range(1, 18)]
    
    # Constraints for flights and city transitions
    for i in range(17):
        # If flying, must have direct flight between current and next city
        s.add(Implies(fly[i], Or(
            And(city[i] == 0, city[i+1] == 1),
            And(city[i] == 1, city[i+1] == 0),
            And(city[i] == 2, city[i+1] == 0),
            And(city[i] == 0, city[i+1] == 2)
        )))
        # If not flying, next city same as current
        s.add(Implies(Not(fly[i]), city[i+1] == city[i]))
    
    # Total days constraints
    split_days = 0
    santorini_days = 0
    london_days = 0
    
    for i in range(18):
        # Count morning city
        split_days += If(city[i] == 2, 1, 0)
        santorini_days += If(city[i] == 1, 1, 0)
        london_days += If(city[i] == 0, 1, 0)
        
        # Count flight days (if flying to this city)
        if i < 17:
            split_days += If(And(fly[i], city[i+1] == 2), 1, 0)
            santorini_days += If(And(fly[i], city[i+1] == 1), 1, 0)
            london_days += If(And(fly[i], city[i+1] == 0), 1, 0)
    
    s.add(split_days == 6)
    s.add(santorini_days == 7)
    s.add(london_days == 7)
    
    # Conference constraints
    s.add(Or(city[11] == 1, And(fly[11], city[12] == 1)))  # Day 12
    s.add(city[17] == 1)  # Day 18
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        
        # Get city for each day (starting city)
        city_values = [m.evaluate(city[i]).as_long() for i in range(18)]
        
        # Get flight decisions
        fly_values = [is_true(m.evaluate(fly[i])) for i in range(17)]
        
        # Compute overnight stays (city at end of each day)
        overnight = []
        for i in range(17):
            if fly_values[i]:
                overnight.append(city_values[i+1])
            else:
                overnight.append(city_values[i])
        overnight.append(city_values[17])  # Day 18
        
        # Generate segments
        segments = []
        start_day = 1
        current_city = overnight[0]
        
        for day in range(1, 18):
            if overnight[day] != current_city:
                segments.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": cities[current_city]
                })
                start_day = day + 1
                current_city = overnight[day]
        
        segments.append({
            "day_range": f"Day {start_day}-18",
            "place": cities[current_city]
        })
        
        # Output JSON
        result = {"itinerary": segments}
        print(json.dumps(result))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()