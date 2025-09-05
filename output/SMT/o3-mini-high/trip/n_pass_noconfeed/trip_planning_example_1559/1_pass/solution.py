from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    N = 10  # total number of cities in itinerary
    # Cities indices: 0: Valencia, 1: Oslo, 2: Lyon, 3: Prague, 4: Paris,
    # 5: Nice, 6: Seville, 7: Tallinn, 8: Mykonos, 9: Lisbon
    cities = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]
    
    # Required durations for each city (if visited in isolation)
    # Note: When moving between cities, the flight day counts in both cities.
    durations = {0: 2, 1: 3, 2: 4, 3: 3, 4: 4, 5: 4, 6: 5, 7: 2, 8: 5, 9: 2}
    
    # Define decision variables:
    # c[i]: which city is visited in position i (an integer 0..9)
    # start[i]: the starting day (arrival day) of the visit for city in position i
    # finish[i]: the finishing day (departure day) for that visit (departure happens on a flight day that is shared with next city's arrival)
    c = [Int(f"c_{i}") for i in range(N)]
    start_days = [Int(f"start_{i}") for i in range(N)]
    finish_days = [Int(f"finish_{i}") for i in range(N)]
    
    # Each city index must be between 0 and 9 and all must be distinct (we visit each city exactly once).
    for i in range(N):
        solver.add(And(c[i] >= 0, c[i] <= 9))
    solver.add(Distinct(c))
    
    # Function to get duration based on city variable using nested If-then-else.
    def get_duration(city_var):
        return If(city_var == 0, 2,
               If(city_var == 1, 3,
               If(city_var == 2, 4,
               If(city_var == 3, 3,
               If(city_var == 4, 4,
               If(city_var == 5, 4,
               If(city_var == 6, 5,
               If(city_var == 7, 2,
               If(city_var == 8, 5,
               If(city_var == 9, 2, 0))))))))))
    
    # Set up time constraints.
    # The trip starts on day 1: start of the first city is day 1.
    solver.add(start_days[0] == 1)
    for i in range(N):
        # The finish day is start day + (duration - 1) (because the flight day is double counted)
        solver.add(finish_days[i] == start_days[i] + get_duration(c[i]) - 1)
        # Each city's visit must be within day 1 and day 25.
        solver.add(start_days[i] >= 1, finish_days[i] <= 25)
        solver.add(finish_days[i] >= start_days[i])
        
    # For consecutive cities, the arrival day of the next is the same as the finish day of the previous (flight day overlap)
    for i in range(1, N):
        solver.add(start_days[i] == finish_days[i-1])
    
    # The trip must finish on day 25.
    solver.add(finish_days[N-1] == 25)
    
    # List of allowed direct flights (bidirectional). Each tuple (a, b) represents a flight between city a and b.
    allowed_flights = [
        (9, 4), (4, 9),
        (2, 5), (5, 2),
        (7, 1), (1, 7),
        (3, 2), (2, 3),
        (4, 1), (1, 4),
        (9, 6), (6, 9),
        (3, 9), (9, 3),
        (1, 5), (5, 1),
        (0, 4), (4, 0),
        (0, 9), (9, 0),
        (4, 5), (5, 4),
        (5, 8), (8, 5),
        (4, 2), (2, 4),
        (0, 2), (2, 0),
        (3, 1), (1, 3),
        (3, 4), (4, 3),
        (6, 4), (4, 6),
        (1, 2), (2, 1),
        (3, 0), (0, 3),
        (9, 5), (5, 9),
        (9, 1), (1, 9),
        (0, 6), (6, 0),
        (9, 2), (2, 9),
        (4, 7), (7, 4),
        (3, 7), (7, 3)
    ]
    
    # For each consecutive city pair in the itinerary, enforce that there is an allowed direct flight.
    for i in range(N - 1):
        flight_options = []
        for (a, b) in allowed_flights:
            flight_options.append(And(c[i] == a, c[i+1] == b))
        solver.add(Or(flight_options))
    
    # Additional event constraints:
    # 1. Valencia (city 0): 2-day stay; meet friends in Valencia between day 3 and day 4.
    #    Constraint: if this city visit is Valencia, then its visit interval must overlap [3,4].
    for i in range(N):
        solver.add(Implies(c[i] == 0, And(finish_days[i] >= 3, start_days[i] <= 4)))
        
    # 2. Oslo (city 1): 3-day stay; meet a friend in Oslo between day 13 and day 15.
    for i in range(N):
        solver.add(Implies(c[i] == 1, And(finish_days[i] >= 13, start_days[i] <= 15)))
        
    # 3. Lyon (city 2): 4-day stay. (No extra event constraint beyond the duration.)
    
    # 4. Prague (city 3): 3-day stay.
    
    # 5. Paris (city 4): 4-day stay.
    
    # 6. Nice (city 5): 4-day stay.
    
    # 7. Seville (city 6): 5-day stay; attend annual show from day 5 to day 9.
    #    Must be in Seville for the whole period of the show.
    for i in range(N):
        solver.add(Implies(c[i] == 6, And(start_days[i] <= 5, finish_days[i] >= 9)))
        
    # 8. Tallinn (city 7): 2-day stay.
    
    # 9. Mykonos (city 8): 5-day stay; attend a wedding in Mykonos between day 21 and day 25.
    for i in range(N):
        solver.add(Implies(c[i] == 8, finish_days[i] >= 21))
        
    # 10. Lisbon (city 9): 2-day stay.
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(N):
            start_val = model[start_days[i]].as_long()
            finish_val = model[finish_days[i]].as_long()
            city_idx = model[c[i]].as_long()
            itinerary.append({"day_range": f"Day {start_val}-{finish_val}", "place": cities[city_idx]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No valid itinerary found."}))

if __name__ == "__main__":
    main()