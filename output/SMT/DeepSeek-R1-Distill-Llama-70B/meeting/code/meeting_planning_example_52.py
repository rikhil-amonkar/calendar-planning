from z3 import *

# Define travel times between locations (in minutes)
travel_times = {
    ('Russian Hill', 'Richmond District'): 14,
    ('Richmond District', 'Russian Hill'): 13,
}

# Define friend's data (time in minutes since midnight)
friends = [
    {
        'name': 'Barbara',
        'location': 'Richmond District',
        'start': 810,   # 1:15 PM
        'end': 1125,    # 6:15 PM
        'duration': 45
    }
]

def main():
    # Create a solver
    s = Solver()

    # Create variables for start times
    var = {friend['name']: Real(f"{friend['name']}_start") for friend in friends}

    # Add constraints for each friend's availability
    for friend in friends:
        s.add(var[friend['name']] >= friend['start'])
        s.add(var[friend['name']] + friend['duration'] <= friend['end'])

    # Since we start at Russian Hill, we don't need to add travel constraints for this problem
    # Check satisfiability
    if s.check() == sat:
        model = s.model()
        print("SOLUTION: You can meet Barbara.")
        print(f"Meet Barbara starting at {model[var['Barbara']]} minutes since midnight.")
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()