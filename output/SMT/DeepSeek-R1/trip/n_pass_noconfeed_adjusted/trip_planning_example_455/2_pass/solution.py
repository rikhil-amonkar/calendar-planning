from z3 import *
import json

def main():
    # Define cities
    RKV, RGA, WAW, IST, KRK = 0, 1, 2, 3, 4
    city_names = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    
    # Direct flights as tuples (from, to) including missing flights
    direct_flights = [
        (0,2), (2,0), (3,2), (2,3), (1,3), (3,1), (4,2), (2,4), (1,2), (2,1), (3,4), (4,3),
        (0,1), (1,0)  # Added missing flights between Reykjavik and Riga
    ]
    
    # Arrays for start and end city for each day (index 0 to 20 for days 1 to 21)
    start_city = [Int(f'start_city_{i+1}') for i in range(21)]
    end_city = [Int(f'end_city_{i+1}') for i in range(21)]
    
    solver = Solver()
    
    # Constrain city values to be between 0 and 4
    for i in range(21):
        solver.add(start_city[i] >= 0, start_city[i] <= 4)
        solver.add(end_city[i] >= 0, end_city[i] <= 4)
    
    # Trip starts in Reykjavik and ends in Krakow
    solver.add(start_city[0] == RKV)
    solver.add(end_city[20] == KRK)
    
    # For days 2 to 21, start city equals previous end city
    for i in range(1, 21):
        solver.add(start_city[i] == end_city[i-1])
    
    # Flight constraints: if start and end city differ, must be direct flight
    for i in range(21):
        flight_constraint = Implies(
            start_city[i] != end_city[i],
            Or([And(start_city[i] == a, end_city[i] == b) for a, b in direct_flights])
        )
        solver.add(flight_constraint)
    
    # Event constraints
    solver.add(end_city[0] == RGA)  # Day 1 ends in Riga
    solver.add(end_city[1] == IST)  # Day 2 ends in Istanbul
    for i in range(2, 7):  # Days 3 to 7 end in Istanbul
        solver.add(end_city[i] == IST)
    
    # Function to compute days spent in a city
    def days_in_city(city):
        total = 0
        for i in range(21):
            # Count a day if the city is the start or end city
            total += If(Or(start_city[i] == city, end_city[i] == city), 1, 0)
        return total
    
    # Total days constraints
    solver.add(days_in_city(RKV) == 7)
    solver.add(days_in_city(RGA) == 2)
    solver.add(days_in_city(WAW) == 3)
    solver.add(days_in_city(IST) == 6)
    solver.add(days_in_city(KRK) == 7)
    
    if solver.check() == sat:
        model = solver.model()
        end_assignments = [model.evaluate(end_city[i]).as_long() for i in range(21)]
        
        itinerary = []
        current_city = end_assignments[0]
        start_day = 1
        for day in range(1, 21):
            if end_assignments[day] != current_city:
                end_day = day
                day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                itinerary.append({"day_range": day_range, "place": city_names[current_city]})
                current_city = end_assignments[day]
                start_day = day + 1
        day_range = f"Day {start_day}-21" if start_day != 21 else "Day 21"
        itinerary.append({"day_range": day_range, "place": city_names[current_city]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()