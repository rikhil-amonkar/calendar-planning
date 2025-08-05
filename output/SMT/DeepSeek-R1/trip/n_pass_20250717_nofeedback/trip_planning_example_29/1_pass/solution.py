from z3 import *

def main():
    # Define the city enum
    City, (dub, frank, krak) = EnumSort('City', ['Dubrovnik', 'Frankfurt', 'Krakow'])
    cities = {dub: "Dubrovnik", frank: "Frankfurt", krak: "Krakow"}
    
    # s0: start city at the beginning of day1
    s0 = Const('s0', City)
    # s: list for end of day1 to day10
    s = [Const(f's_{i}', City) for i in range(1, 11)]
    
    # Direct flight pairs
    direct_flights = [(dub, frank), (frank, dub), (frank, krak), (krak, frank)]
    
    constraints = []
    
    # Flight constraint for day1: from s0 to s[0]
    constraints.append(
        If(s0 != s[0],
            Or(
                And(s0 == dub, s[0] == frank),
                And(s0 == frank, s[0] == dub),
                And(s0 == frank, s[0] == krak),
                And(s0 == krak, s[0] == frank)
            ),
            True
        )
    )
    
    # Flight constraints for transitions from day i to i+1 (i from 1 to 9)
    for i in range(0, 9):
        constraints.append(
            If(s[i] != s[i+1],
                Or(
                    And(s[i] == dub, s[i+1] == frank),
                    And(s[i] == frank, s[i+1] == dub),
                    And(s[i] == frank, s[i+1] == krak),
                    And(s[i] == krak, s[i+1] == frank)
                ),
                True
            )
        )
    
    # Count days for Dubrovnik
    count_dub = 0
    # Flight-out on day1 if started in Dubrovnik and then left
    count_dub += If(And(s0 == dub, s[0] != dub), 1, 0)
    # Days ending in Dubrovnik
    for i in range(10):
        count_dub += If(s[i] == dub, 1, 0)
    # Flight-outs on days 2 to 10: for j in 2..10, flight-out on day j: if s[j-2] (end of day j-1) is Dubrovnik and s[j-1] (end of day j) is not
    for j in range(1, 10):  # j from 1 to 9: then we look at s[j-1] and s[j] for flight-out on day j+1? 
        # Actually, we want flight-out on day j+1: which requires start of day j+1 (s[j]) and leave on day j+1 (s[j] to s[j+1] not same? 
        # But note: we are looking at consecutive pairs: s[i] and s[i+1] for flight-out on day i+2? 
        # Correction: flight-out on day j is captured by the pair (s[j-2], s[j-1]) for j>=2. 
        # Since j from 2 to 10, we let i = j-2, then i from 0 to 8.
        # But in our loop j from 1 to 9, we are actually covering the pairs (s[0],s[1]) to (s[8],s[9]) for flight-outs on days 2 to 10.
        # Because: 
        #   For flight-out on day2: we look at s0 and s[0]? -> already done separately for day1 flight-out.
        #   For flight-out on day2: we start day2 in s[0] (end of day1) and leave to s[1] (end of day2) -> so if s[0]==dub and s[1]!=dub, then flight-out on day2.
        #   Therefore, we do:
        count_dub += If(And(s[j-1] == dub, s[j] != dub), 1, 0)
    constraints.append(count_dub == 7)
    
    # Count days for Frankfurt
    count_frank = 0
    count_frank += If(And(s0 == frank, s[0] != frank), 1, 0)
    for i in range(10):
        count_frank += If(s[i] == frank, 1, 0)
    for j in range(1, 10):
        count_frank += If(And(s[j-1] == frank, s[j] != frank), 1, 0)
    constraints.append(count_frank == 3)
    
    # Count days for Krakow
    count_krak = 0
    count_krak += If(And(s0 == krak, s[0] != krak), 1, 0)
    for i in range(10):
        count_krak += If(s[i] == krak, 1, 0)
    for j in range(1, 10):
        count_krak += If(And(s[j-1] == krak, s[j] != krak), 1, 0)
    constraints.append(count_krak == 2)
    
    # Wedding constraint: must be in Krakow on day9 or day10
    # For day9: 
    #   Option1: end day9 in Krakow -> s[8] (since s[8] is end of day9) is krak
    #   Option2: start day9 in Krakow (so end of day8 is krak) and leave during day9 (so end of day9 is not krak) -> s[7]==krak and s[8]!=krak
    inKrakow9 = Or(s[8] == krak, And(s[7] == krak, s[8] != krak))
    # For day10:
    #   Option1: end day10 in Krakow -> s[9]==krak
    #   Option2: start day10 in Krakow (s[8]==krak) and leave during day10 (s[9]!=krak)
    inKrakow10 = Or(s[9] == krak, And(s[8] == krak, s[9] != krak))
    constraints.append(Or(inKrakow9, inKrakow10))
    
    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        # Get the start city s0
        s0_val = model[s0]
        s_vals = [model[s_i] for s_i in s]
        
        # Build the itinerary: for each day, the city at the end of the day
        itinerary = []
        for day in range(1, 11):
            # s_vals index: day1 -> index0, day10 -> index9
            city_sym = s_vals[day-1]
            city_name = cities[city_sym]
            itinerary.append({"day": day, "city": city_name})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()