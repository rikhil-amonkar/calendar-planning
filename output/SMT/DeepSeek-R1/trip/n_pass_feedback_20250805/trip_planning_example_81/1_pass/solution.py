from z3 import *
import json

def main():
    # Create the Z3 solver
    s = Solver()

    # City indices: 0: Mykonos, 1: Budapest, 2: Hamburg
    num_days = 9
    num_cities = 3

    # Create a 2D list for the variables: in_day[day][city_index]
    in_day = [[None for _ in range(num_cities)] for _ in range(num_days + 1)]  # 1-indexed days: 1..9

    # Initialize variables
    for day in range(1, num_days + 1):
        for c in range(num_cities):
            in_day[day][c] = Bool(f"in_{day}_{c}")

    # Fixed constraints: Must be in Mykonos on day 4 and day 9
    s.add(in_day[4][0] == True)
    s.add(in_day[9][0] == True)

    # Total days constraints
    total_mykonos = 0
    total_budapest = 0
    total_hamburg = 0
    for day in range(1, num_days + 1):
        total_mykonos += If(in_day[day][0], 1, 0)
        total_budapest += If(in_day[day][1], 1, 0)
        total_hamburg += If(in_day[day][2], 1, 0)
    s.add(total_mykonos == 6)
    s.add(total_budapest == 3)
    s.add(total_hamburg == 2)

    # Constraints for each day: must be in 1 or 2 cities, and if 2 cities, they must be adjacent
    for day in range(1, num_days + 1):
        v0 = in_day[day][0]  # Mykonos
        v1 = in_day[day][1]  # Budapest
        v2 = in_day[day][2]  # Hamburg
        num_cities_day = If(v0, 1, 0) + If(v1, 1, 0) + If(v2, 1, 0)
        s.add(Or(num_cities_day == 1, num_cities_day == 2))
        # If two cities, they must be adjacent: (Mykonos and Budapest) or (Budapest and Hamburg)
        s.add(Implies(num_cities_day == 2, Or(And(v0, v1), And(v1, v2))))

    # Continuity constraints between consecutive days
    for day in range(1, num_days):
        s.add(Or(
            And(in_day[day][0], in_day[day + 1][0]),  # Mykonos consecutive
            And(in_day[day][1], in_day[day + 1][1]),  # Budapest consecutive
            And(in_day[day][2], in_day[day + 1][2])   # Hamburg consecutive
        ))

    # Solve the problem
    if s.check() == sat:
        model = s.model()
        # Map city indices to names
        city_names = {0: "Mykonos", 1: "Budapest", 2: "Hamburg"}
        itinerary_list = []
        for day in range(1, num_days + 1):
            cities_today = []
            for c in range(num_cities):
                if model.evaluate(in_day[day][c]):
                    cities_today.append(city_names[c])
            cities_today.sort()  # Sort alphabetically: Budapest, Hamburg, Mykonos
            place_str = ", ".join(cities_today)
            itinerary_list.append({"day": day, "place": place_str})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()