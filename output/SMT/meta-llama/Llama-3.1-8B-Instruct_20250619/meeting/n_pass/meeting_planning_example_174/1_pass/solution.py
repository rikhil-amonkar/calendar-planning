from z3 import *

# Define the travel times in minutes
travel_times = {
    'Nob Hill to Pacific Heights': 8,
    'Nob Hill to Mission District': 13,
    'Pacific Heights to Nob Hill': 8,
    'Pacific Heights to Mission District': 15,
    'Mission District to Nob Hill': 12,
    'Mission District to Pacific Heights': 16
}

# Define the constraints
arrive_time = 0
leaves_thomas = 7*60 + 15  # 7:15 PM
min_time_with_thomas = 75
leaves_kenneth = 3*60 + 45  # 3:45 PM
min_time_with_kenneth = 45

# Define the variables
x1 = Int('x1')  # Time to travel from Nob Hill to Pacific Heights
x2 = Int('x2')  # Time to travel from Nob Hill to Mission District
x3 = Int('x3')  # Time to travel from Pacific Heights to Nob Hill
x4 = Int('x4')  # Time to travel from Pacific Heights to Mission District
x5 = Int('x5')  # Time to travel from Mission District to Nob Hill
x6 = Int('x6')  # Time to travel from Mission District to Pacific Heights
y1 = Int('y1')  # Time to meet Thomas
y2 = Int('y2')  # Time to meet Kenneth

# Define the solver
solver = Solver()

# Add constraints
solver.add(arrive_time + x1 <= y1)
solver.add(y1 <= arrive_time + x1 + travel_times['Pacific Heights to Nob Hill'] + leaves_thomas - min_time_with_thomas)
solver.add(arrive_time + x2 <= y2)
solver.add(y2 <= arrive_time + x2 + travel_times['Mission District to Nob Hill'] + leaves_kenneth - min_time_with_kenneth)
solver.add(y1 >= min_time_with_thomas)
solver.add(y2 >= min_time_with_kenneth)

# Try all possible combinations of travel times
for x1_val in range(0, 61):
    for x2_val in range(0, 61):
        for x3_val in range(0, 61):
            for x4_val in range(0, 61):
                for x5_val in range(0, 61):
                    for x6_val in range(0, 61):
                        solver.push()
                        solver.add(x1 == x1_val)
                        solver.add(x2 == x2_val)
                        solver.add(x3 == x3_val)
                        solver.add(x4 == x4_val)
                        solver.add(x5 == x5_val)
                        solver.add(x6 == x6_val)
                        result = solver.check()
                        if result == sat:
                            model = solver.model()
                            y1_val = model[y1].as_long()
                            y2_val = model[y2].as_long()
                            print(f"Travel times: x1={x1_val}, x2={x2_val}, x3={x3_val}, x4={x4_val}, x5={x5_val}, x6={x6_val}")
                            print(f"Meeting times: y1={y1_val}, y2={y2_val}")
                        solver.pop()

print("No solution found.")