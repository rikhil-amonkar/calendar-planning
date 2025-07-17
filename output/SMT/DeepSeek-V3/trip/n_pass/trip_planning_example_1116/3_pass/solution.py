from z3 import *

def solve_scheduling_problem():
    # Define the cities
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    
    # Direct flights as a set of tuples
    direct_flights = {
        ("Reykjavik", "Munich"), ("Munich", "Frankfurt"), ("Split", "Oslo"), ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"), ("Oslo", "Frankfurt"), ("Bucharest", "Barcelona"), ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"), ("Barcelona", "Stockholm"), ("Barcelona", "Reykjavik"), ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"), ("Bucharest", "Oslo"), ("Bucharest", "Frankfurt"), ("Split", "Stockholm"),
        ("Barcelona", "Oslo"), ("Stockholm", "Munich"), ("Stockholm", "Oslo"), ("Split", "Frankfurt"),
        ("Barcelona", "Munich"), ("Stockholm", "Frankfurt"), ("Munich", "Oslo"), ("Split", "Munich")
    }
    
    # Create a symmetric direct flights set (i.e., if (A,B) is in the set, so is (B,A))
    symmetric_flights = set()
    for (a, b) in direct_flights:
        symmetric_flights.add((a, b))
        symmetric_flights.add((b, a))
    direct_flights = symmetric_flights
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Create variables: day_1 to day_20, each can be one of the cities
    days = [Int(f"day_{i}") for i in range(1, 21)]
    
    # Each day variable must be between 0 and 7 (representing the 8 cities)
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}
    
    for day in days:
        solver.add(day >= 0, day <= 7)
    
    # Constraints for city durations:
    # Oslo: 2 days (including day 16-17)
    # Reykjavik: 5 days (including a day between 9-13)
    # Stockholm: 4 days
    # Munich: 4 days (including days 13-16)
    # Frankfurt: 4 days (including days 17-20)
    # Barcelona: 3 days
    # Bucharest: 2 days
    # Split: 3 days
    
    # Count occurrences of each city in the days
    city_counts = []
    for city_num in range(8):
        count = Sum([If(day == city_num, 1, 0) for day in days])
        city_counts.append(count)
    
    solver.add(city_counts[city_to_num["Oslo"]] == 2)
    solver.add(city_counts[city_to_num["Reykjavik"]] == 5)
    solver.add(city_counts[city_to_num["Stockholm"]] == 4)
    solver.add(city_counts[city_to_num["Munich"]] == 4)
    solver.add(city_counts[city_to_num["Frankfurt"]] == 4)
    solver.add(city_counts[city_to_num["Barcelona"]] == 3)
    solver.add(city_counts[city_to_num["Bucharest"]] == 2)
    solver.add(city_counts[city_to_num["Split"]] == 3)
    
    # Specific day constraints:
    # Oslo must be on days 16 and 17
    solver.add(days[15] == city_to_num["Oslo"])  # day 16 is index 15 (0-based)
    solver.add(days[16] == city_to_num["Oslo"])   # day 17 is index 16
    
    # Reykjavik must include at least one day between 9-13 (days 9 to 13 are indices 8 to 12)
    solver.add(Or([days[i] == city_to_num["Reykjavik"] for i in range(8, 13)]))
    
    # Munich must include days 13-16 (indices 12 to 15)
    # At least one of these days must be Munich
    solver.add(Or([days[i] == city_to_num["Munich"] for i in range(12, 16)]))
    
    # Frankfurt must include days 17-20 (indices 16 to 19)
    solver.add(Or([days[i] == city_to_num["Frankfurt"] for i in range(16, 20)]))
    
    # Flight constraints: adjacent days in different cities must have a direct flight
    for i in range(19):  # days 1..20, so adjacent pairs are (0,1), (1,2), ..., (18,19)
        day_current = days[i]
        day_next = days[i+1]
        # Either same city or connected by a direct flight
        solver.add(Or(
            day_current == day_next,
            *[And(day_current == city_to_num[a], day_next == city_to_num[b]) for (a, b) in direct_flights]
        ))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(20):
            day_num = i + 1
            city_num = model.evaluate(days[i]).as_long()
            city = num_to_city[city_num]
            itinerary.append({"day": day_num, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
result = solve_scheduling_problem()
print(result)