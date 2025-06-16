from z3 import *

def main():
    # Define the city constants
    Brussels, Barcelona, Split = 0, 1, 2
    cities = {Brussels: 'Brussels', Barcelona: 'Barcelona', Split: 'Split'}
    
    # s[0] to s[12]: s[i] is the city at the start of day i+1
    s = IntVector('s', 13)
    # fly[0] to fly[11]: fly[i] is True if flying on day i+1
    fly = BoolVector('fly', 12)
    
    solver = Solver()
    
    # Constraint: Start in Brussels on day 1
    solver.add(s[0] == Brussels)
    
    # Constraints for each day i from 0 to 11 (day1 to day12)
    for i in range(12):
        # Ensure s[i] is a valid city (0, 1, or 2)
        solver.add(s[i] >= Brussels, s[i] <= Split)
        
        # Flight constraints: if flying, the flight must be direct; else, stay in the same city
        solver.add(If(fly[i],
                     Or(
                         And(s[i] == Brussels, s[i+1] == Barcelona),
                         And(s[i] == Barcelona, s[i+1] == Brussels),
                         And(s[i] == Barcelona, s[i+1] == Split),
                         And(s[i] == Split, s[i+1] == Barcelona)
                     ),
                     s[i+1] == s[i]
                  ))
    
    # Define presence in each city per day
    InBrussels = [None] * 12
    InBarcelona = [None] * 12
    InSplit = [None] * 12
    
    for i in range(12):
        # On day i+1: if not flying, present only in s[i]; if flying, present in both s[i] and s[i+1]
        InBrussels[i] = Or(And(Not(fly[i]), s[i] == Brussels), And(fly[i], Or(s[i] == Brussels, s[i+1] == Brussels)))
        InBarcelona[i] = Or(And(Not(fly[i]), s[i] == Barcelona), And(fly[i], Or(s[i] == Barcelona, s[i+1] == Barcelona)))
        InSplit[i] = Or(And(Not(fly[i]), s[i] == Split), And(fly[i], Or(s[i] == Split, s[i+1] == Split)))
    
    # Sum the days in each city
    count_Brussels = Sum([If(InBrussels[i], 1, 0) for i in range(12)])
    count_Barcelona = Sum([If(InBarcelona[i], 1, 0) for i in range(12)])
    count_Split = Sum([If(InSplit[i], 1, 0) for i in range(12)])
    
    # Add the required day counts
    solver.add(count_Brussels == 2)
    solver.add(count_Barcelona == 7)
    solver.add(count_Split == 5)
    
    # Ensure present in Brussels on day 2 (index 1)
    solver.add(InBrussels[1] == True)
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.evaluate(s[i]).as_long() for i in range(13)]
        fly_val = [m.evaluate(fly[i]) for i in range(12)]
        
        # Print the itinerary
        for day in range(1, 13):
            idx = day - 1
            current_city = cities[s_val[idx]]
            if fly_val[idx]:
                next_city = cities[s_val[idx+1]]
                print(f"Day {day}: Fly from {current_city} to {next_city} (spend day in both {current_city} and {next_city})")
            else:
                print(f"Day {day}: Stay in {current_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()