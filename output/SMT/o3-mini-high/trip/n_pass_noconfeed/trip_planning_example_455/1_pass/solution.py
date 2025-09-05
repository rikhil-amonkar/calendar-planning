from z3 import *
import json

def main():
    # Create solver
    solver = Solver()

    # Define cities with indices:
    # 0: Reykjavik, 1: Riga, 2: Warsaw, 3: Istanbul, 4: Krakow
    city_names = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
    
    # Durations per city (as given)
    # Note: The “city day count” sums to 25 (with 4 overlapping transit days) giving a 21‐day itinerary.
    durations = [7, 2, 3, 6, 7]  

    # Create variables for the itinerary order (5 positions; each must be among 0..4 and all distinct)
    itinerary = [Int(f"itinerary_{i}") for i in range(5)]
    for i in range(5):
        solver.add(itinerary[i] >= 0, itinerary[i] <= 4)
    solver.add(Distinct(itinerary))
    
    # Create variables for the start day of each segment (S_0 .. S_4)
    S = [Int(f"S_{i}") for i in range(5)]
    # The trip starts on day 1
    solver.add(S[0] == 1)

    # Define a helper function: given a city variable, return its duration (using If-then-else)
    def seg_duration(city_var):
        return If(city_var == 0, 7,
               If(city_var == 1, 2,
               If(city_var == 2, 3,
               If(city_var == 3, 6, 7))))
    
    # Link the segments in time.
    # The rule is: if you fly from city A to city B on day X, then
    # city A is visited until day X and city B is visited starting on day X.
    # Thus for segment i, if its duration is d then its end day is S[i] + d - 1, and S[i+1] equals that end day.
    for i in range(4):
        solver.add(S[i+1] == S[i] + seg_duration(itinerary[i]) - 1)
    # The final segment’s end day must be day 21.
    solver.add(S[4] + seg_duration(itinerary[4]) - 1 == 21)

    # Allowed direct flight transitions.
    # Direct flights exist between (bidirectionally):
    # Istanbul & Krakow, Warsaw & Reykjavik, Istanbul & Warsaw, Riga & Istanbul, Krakow & Warsaw, Riga & Warsaw.
    def allowed_transition(city_a, city_b):
        return Or(
            And(city_a == 0, city_b == 2),  # Reykjavik <-> Warsaw
            And(city_a == 2, city_b == 0),
            And(city_a == 3, city_b == 4),  # Istanbul <-> Krakow
            And(city_a == 4, city_b == 3),
            And(city_a == 3, city_b == 2),  # Istanbul <-> Warsaw
            And(city_a == 2, city_b == 3),
            And(city_a == 1, city_b == 3),  # Riga <-> Istanbul
            And(city_a == 3, city_b == 1),
            And(city_a == 4, city_b == 2),  # Krakow <-> Warsaw
            And(city_a == 2, city_b == 4),
            And(city_a == 1, city_b == 2),  # Riga <-> Warsaw
            And(city_a == 2, city_b == 1)
        )
    
    # Enforce that subsequent cities in the itinerary must be connected by a direct flight.
    for i in range(4):
        solver.add(allowed_transition(itinerary[i], itinerary[i+1]))
    
    # Event constraints:
    # - Meet a friend in Riga (city index 1) between overall day 1 and day 2.
    # - Attend a wedding in Istanbul (city index 3) between overall day 2 and day 7.
    friend_meet_day = Int("friend_meet_day")
    solver.add(friend_meet_day >= 1, friend_meet_day <= 2)
    wedding_day = Int("wedding_day")
    solver.add(wedding_day >= 2, wedding_day <= 7)
    
    # For the segment where the city is Riga (city index 1), the friend meeting must occur during that city’s stay.
    # Since Riga’s duration is 2 days, the visit spans days S[i] to S[i] + 1.
    for i in range(5):
        solver.add(Implies(itinerary[i] == 1, And(friend_meet_day >= S[i], friend_meet_day <= S[i] + 1)))
        
    # For the segment where the city is Istanbul (city index 3), the wedding must occur during that city’s stay.
    # Istanbul’s duration is 6 days, so the visit spans days S[i] to S[i] + 5.
    for i in range(5):
        solver.add(Implies(itinerary[i] == 3, And(wedding_day >= S[i], wedding_day <= S[i] + 5)))
    
    # Check for satisfiability and extract the model.
    if solver.check() == sat:
        model = solver.model()
        segments = []
        for i in range(5):
            city_val = model[itinerary[i]].as_long()
            start_day = model[S[i]].as_long()
            # Determine the duration based on the city
            if city_val == 0:
                d = 7
            elif city_val == 1:
                d = 2
            elif city_val == 2:
                d = 3
            elif city_val == 3:
                d = 6
            elif city_val == 4:
                d = 7
            end_day = start_day + d - 1
            segments.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_val]
            })
        output = {"itinerary": segments}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()