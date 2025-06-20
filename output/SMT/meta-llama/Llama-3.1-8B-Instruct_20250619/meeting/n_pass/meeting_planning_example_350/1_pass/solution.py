from z3 import *

# Define the travel times
travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

# Define the constraints
s = Optimize()

# Define the variables
start_time = 0
end_time = 24 * 60  # 24 hours in minutes
x = [Bool(f"visit_{location}") for location in travel_times.keys()]
y = [Int(f"stay_{location}") for location in travel_times.keys()]

# Define the objective function
obj = [x[i] * (travel_times[tuple(sorted(list(k.split(" to ")[0], list(k.split(" to ")[1]))))] + y[i]) for i, k in enumerate(travel_times.keys())]
s.add(Maximize(Sum(obj)))

# Define the constraints
s.add(And([start_time + travel_times[tuple(sorted(list(k.split(" to ")[0], list(k.split(" to ")[1]))))]*x[i] <= start_time + y[i] + travel_times[tuple(sorted(list(k.split(" to ")[0], list(k.split(" to ")[1]))))]*x[i+1] for i, k in enumerate(travel_times.keys()) if i < len(travel_times.keys())-1]))
s.add(And([start_time + travel_times[tuple(sorted(list(k.split(" to ")[0], list(k.split(" to ")[1]))))]*x[i] >= start_time + y[i] for i, k in enumerate(travel_times.keys())]))
s.add(And([start_time + y[i] + travel_times[tuple(sorted(list(k.split(" to ")[0], list(k.split(" to ")[1]))))]*x[i+1] <= end_time for i, k in enumerate(travel_times.keys()) if i < len(travel_times.keys())-1]))
s.add(Or([x[i] for i, k in enumerate(travel_times.keys())]))
s.add(And([x[i] == 0 for i, k in enumerate(travel_times.keys()) if k.split(" to ")[0] == "Bayview" and i < 4]))
s.add(And([x[i] == 0 for i, k in enumerate(travel_times.keys()) if k.split(" to ")[1] == "Bayview" and i > 3]))
s.add(And([y[i] >= 45 for i, k in enumerate(travel_times.keys()) if "Pacific Heights" in k]))
s.add(And([y[i] >= 75 for i, k in enumerate(travel_times.keys()) if "Mission District" in k]))
s.add(And([y[i] >= 90 for i, k in enumerate(travel_times.keys()) if "Haight-Ashbury" in k]))
s.add(And([y[i] >= 120 for i, k in enumerate(travel_times.keys()) if "Financial District" in k]))

# Solve the problem
result = s.check()
if result == sat:
    m = s.model()
    schedule = []
    for i, k in enumerate(travel_times.keys()):
        if m.evaluate(x[i]).as_bool():
            schedule.append(k)
    print("SOLUTION:")
    for location in schedule:
        print(f"Visit {location}")
    print(f"Total time: {m.evaluate(s.objective()).as_long()} minutes")
else:
    print("No solution found")