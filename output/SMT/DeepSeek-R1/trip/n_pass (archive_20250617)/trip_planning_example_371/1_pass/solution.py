from z3 import *

def main():
    # Define the City enum
    City = Datatype('City')
    City.declare('Vienna')
    City.declare('Stockholm')
    City.declare('Nice')
    City.declare('Split')
    City = City.create()
    
    # Create variables for the starting city of each day (days 1 to 9)
    s = [ Const('s_' + str(i), City) for i in range(1,10) ]
    
    solver = Solver()
    
    # Allowed direct flight pairs (both directions)
    allowed_pairs = [
        (City.Vienna, City.Stockholm),
        (City.Vienna, City.Nice),
        (City.Vienna, City.Split),
        (City.Stockholm, City.Split),
        (City.Nice, City.Stockholm)
    ]
    allowed_directed = []
    for pair in allowed_pairs:
        allowed_directed.append(pair)
        allowed_directed.append((pair[1], pair[0]))
    
    # Flight constraints: if two consecutive days have different starting cities, the pair must be in allowed_directed
    for i in range(0, 8):  # from day1 to day8 (flights on day1 to day8)
        constraint = Or([ And(s[i] == a, s[i+1] == b) for (a, b) in allowed_directed ])
        solver.add(If(s[i] != s[i+1], constraint, True))
    
    # Function to compute total days in a city
    def total_days(city):
        # Days where the day starts in the city
        start_days = Sum([If(s[i] == city, 1, 0) for i in range(0, 9)])
        # Days where a flight arrives in the city (next day starts here, and flight occurred)
        flight_arrivals = Sum([If(And(s[i] != s[i+1], s[i+1] == city), 1, 0) for i in range(0, 8)])
        return start_days + flight_arrivals
    
    # Add constraints for total days in each city
    solver.add(total_days(City.Nice) == 2
    solver.add(total_days(City.Stockholm) == 5
    solver.add(total_days(City.Split) == 3
    solver.add(total_days(City.Vienna) == 2)
    
    # Constraint: Must be in Split on day7 and day9
    # Day7: either start in Split or fly to Split (so next day starts in Split and flight occurred)
    solver.add(Or(s[6] == City.Split, And(s[6] != s[7], s[7] == City.Split)))
    # Day9: must start in Split (since no flight on day9)
    solver.add(s[8] == City.Split)
    
    # Constraint: Must be in Vienna on day1 and day2
    # Day1: either start in Vienna or fly to Vienna (so next day starts in Vienna and flight occurred)
    solver.add(Or(s[0] == City.Vienna, And(s[0] != s[1], s[1] == City.Vienna)))
    # Day2: either start in Vienna or fly to Vienna (so next day starts in Vienna and flight occurred)
    solver.add(Or(s[1] == City.Vienna, And(s[1] != s[2], s[2] == City.Vienna)))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Get the starting city for each day
        start_cities = [model.evaluate(s_i) for s_i in s]
        # Print the itinerary
        print("Day-by-Day Itinerary:")
        for day in range(0, 9):
            day_num = day + 1
            cities_today = []
            # Always include the starting city of the day
            start_city = start_cities[day]
            cities_today.append(str(start_city))
            # If there's a flight on this day (to next day's starting city), include the arrival city
            if day < 8 and start_cities[day] != start_cities[day+1]:
                cities_today.append(str(start_cities[day+1]))
            # Format the cities for this day
            print(f"Day {day_num}: {' and '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()