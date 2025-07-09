from z3 import *

def solve_itinerary():
    # Define the cities
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Define the direct flights as a dictionary for easy lookup
    direct_flights = {
        "London": ["Amsterdam", "Bucharest", "Frankfurt", "Stockholm"],
        "Amsterdam": ["London", "Stockholm", "Frankfurt", "Riga", "Vilnius", "Bucharest"],
        "Vilnius": ["Frankfurt", "Riga", "Amsterdam"],
        "Frankfurt": ["Vilnius", "Amsterdam", "Stockholm", "Riga", "Bucharest", "London"],
        "Riga": ["Vilnius", "Stockholm", "Frankfurt", "Bucharest", "Amsterdam"],
        "Stockholm": ["Riga", "Amsterdam", "Frankfurt", "London"],
        "Bucharest": ["London", "Riga", "Amsterdam", "Frankfurt"]
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Define variables for each day's city
    day_city = [Int(f"day_{i}_city") for i in range(1, 16)]
    
    # Assign each day to a city (0: Riga, 1: Frankfurt, 2: Amsterdam, 3: Vilnius, 4: London, 5: Stockholm, 6: Bucharest)
    for day in day_city:
        solver.add(day >= 0, day <= 6)
    
    # Constraints for city durations
    # Riga: 2 days
    solver.add(Sum([If(day_city[i] == city_to_index["Riga"], 1, 0) for i in range(15)) == 2)
    # Frankfurt: 3 days
    solver.add(Sum([If(day_city[i] == city_to_index["Frankfurt"], 1, 0) for i in range(15)) == 3)
    # Amsterdam: 2 days, must include day 2-3
    solver.add(Sum([If(day_city[i] == city_to_index["Amsterdam"], 1, 0) for i in range(15)) == 2)
    solver.add(Or(day_city[1] == city_to_index["Amsterdam"], day_city[2] == city_to_index["Amsterdam"]))
    # Vilnius: 5 days, must include days 7-11
    solver.add(Sum([If(day_city[i] == city_to_index["Vilnius"], 1, 0) for i in range(15)) == 5)
    solver.add(Or([day_city[i] == city_to_index["Vilnius"] for i in range(6, 11)]))
    # London: 2 days
    solver.add(Sum([If(day_city[i] == city_to_index["London"], 1, 0) for i in range(15)) == 2)
    # Stockholm: 3 days, must include days 13-15
    solver.add(Sum([If(day_city[i] == city_to_index["Stockholm"], 1, 0) for i in range(15)) == 3)
    solver.add(Or([day_city[i] == city_to_index["Stockholm"] for i in range(12, 15)]))
    # Bucharest: 4 days
    solver.add(Sum([If(day_city[i] == city_to_index["Bucharest"], 1, 0) for i in range(15)) == 4)
    
    # Constraints for flight transitions
    for i in range(14):
        solver.add(Implies(day_city[i] != day_city[i+1], 
                          Or([And(day_city[i] == city_to_index[c1], day_city[i+1] == city_to_index[c2]) 
                              for c1 in direct_flights for c2 in direct_flights[c1]])))
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(15):
            city_index = model[day_city[i]].as_long()
            itinerary.append({"day_range": f"Day {i+1}", "place": cities[city_index]})
        # Group consecutive days in the same city
        grouped_itinerary = []
        current_place = itinerary[0]["place"]
        start_day = 1
        for i in range(1, 15):
            if itinerary[i]["place"] != current_place:
                grouped_itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                grouped_itinerary.append({"day_range": f"Day {i}", "place": current_place})
                grouped_itinerary.append({"day_range": f"Day {i}", "place": itinerary[i]["place"]})
                current_place = itinerary[i]["place"]
                start_day = i + 1
        grouped_itinerary.append({"day_range": f"Day {start_day}-15", "place": current_place})
        return {"itinerary": grouped_itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Print the itinerary
print(solve_itinerary())