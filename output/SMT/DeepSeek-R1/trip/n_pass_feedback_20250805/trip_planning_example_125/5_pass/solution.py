from z3 import *

def main():
    # Define the City enumeration
    City, (Manchester, Seville, Stuttgart) = EnumSort('City', ['Manchester', 'Seville', 'Stuttgart'])
    
    # s0: starting city on day1
    s0 = Const('s0', City)
    # c for end city of each day (c0 for day1, c1 for day2, ... c14 for day15)
    c = [ Const('c_%d' % i, City) for i in range(15) ]
    
    solver = Solver()
    
    # Define direct flight pairs
    def is_direct(a, b):
        return Or(
            And(a == Manchester, b == Seville),
            And(a == Seville, b == Manchester),
            And(a == Stuttgart, b == Manchester),
            And(a == Manchester, b == Stuttgart)
        )
    
    stuttgart_days = []
    seville_days = []
    manchester_days = []
    
    for i in range(15):
        if i == 0:
            start_i = s0
        else:
            start_i = c[i-1]
        end_i = c[i]
        
        # Fixed: added missing closing parenthesis
        solver.add(Or(start_i == end_i, is_direct(start_i, end_i)))
        
        # Track days: city appears if it's start or end city
        stuttgart_days.append(Or(start_i == Stuttgart, end_i == Stuttgart))
        seville_days.append(Or(start_i == Seville, end_i == Seville))
        manchester_days.append(Or(start_i == Manchester, end_i == Manchester))
    
    # Total days constraints
    stuttgart_total = Sum([If(b, 1, 0) for b in stuttgart_days])
    seville_total = Sum([If(b, 1, 0) for b in seville_days])
    manchester_total = Sum([If(b, 1, 0) for b in manchester_days])
    
    solver.add(stuttgart_total == 6)
    solver.add(seville_total == 7)
    solver.add(manchester_total == 4)
    
    # Constraint: visit Stuttgart between days 1-6 (indices 0-5)
    solver.add(Or([stuttgart_days[i] for i in range(6)]))
    
    # Solve and output itinerary
    if solver.check() == sat:
        model = solver.model()
        # Get the end city for each day
        end_cities = []
        for i in range(15):
            city_val = model[c[i]]
            if model.evaluate(city_val == Manchester):
                end_cities.append("Manchester")
            elif model.evaluate(city_val == Seville):
                end_cities.append("Seville")
            elif model.evaluate(city_val == Stuttgart):
                end_cities.append("Stuttgart")
            else:
                end_cities.append("Unknown")
        
        # Group consecutive days with the same end city
        itinerary = []
        start_day = 1
        current_city = end_cities[0]
        
        for day in range(1, 15):
            if end_cities[day] != current_city:
                # Save current block
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": current_city
                })
                # Start new block
                start_day = day + 1
                current_city = end_cities[day]
        
        # Add the last block
        itinerary.append({
            "day_range": f"Day {start_day}-15",
            "place": current_city
        })
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()