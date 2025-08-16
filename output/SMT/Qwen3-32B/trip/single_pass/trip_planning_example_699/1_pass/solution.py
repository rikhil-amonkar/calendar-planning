from z3 import *
import json

# Define cities as integers for easier handling
HAMBURG = 0
DUBLIN = 1
REYKJAVIK = 2
LONDON = 3
HEL_SINKI = 4
MYKONOS = 5

durations = [2, 5, 2, 5, 4, 3]

# Define flight connections
flight_matrix = [[False for _ in range(6)] for _ in range(6)]

flight_matrix[HAMBURG][DUBLIN] = True
flight_matrix[DUBLIN][HAMBURG] = True

flight_matrix[HAMBURG][LONDON] = True
flight_matrix[LONDON][HAMBURG] = True

flight_matrix[HAMBURG][HEL_SINKI] = True
flight_matrix[HEL_SINKI][HAMBURG] = True

flight_matrix[DUBLIN][LONDON] = True
flight_matrix[LONDON][DUBLIN] = True

flight_matrix[DUBLIN][HEL_SINKI] = True
flight_matrix[HEL_SINKI][DUBLIN] = True

flight_matrix[DUBLIN][REYKJAVIK] = True
flight_matrix[REYKJAVIK][DUBLIN] = True

flight_matrix[REYKJAVIK][LONDON] = True
flight_matrix[LONDON][REYKJAVIK] = True

flight_matrix[HEL_SINKI][REYKJAVIK] = True
flight_matrix[REYKJAVIK][HEL_SINKI] = True

flight_matrix[LONDON][HEL_SINKI] = True
flight_matrix[HEL_SINKI][LONDON] = True

flight_matrix[LONDON][MYKONOS] = True
flight_matrix[MYKONOS][LONDON] = True

# Create solver
s = Solver()

# Define order variables
order = [Int(f'order_{i}') for i in range(6)]

# Add constraints for order variables
for i in range(6):
    s.add(And(order[i] >= 0, order[i] < 6))
s.add(Distinct(order))

# Add flight constraints between consecutive cities
for i in range(5):
    current = order[i]
    next_c = order[i+1]
    for a in range(6):
        for b in range(6):
            if not flight_matrix[a][b]:
                s.add(Not(And(current == a, next_c == b)))

# Define start_day variables
start_day = [Int(f'start_day_{i}') for i in range(6)]
s.add(start_day[0] == 1)

for i in range(1, 6):
    prev_city = order[i-1]
    # Compute duration_prev
    duration_prev = If(prev_city == HAMBURG, 2,
        If(prev_city == DUBLIN, 5,
        If(prev_city == REYKJAVIK, 2,
        If(prev_city == LONDON, 5,
        If(prev_city == HEL_SINKI, 4,
        If(prev_city == MYKONOS, 3, 0 )))))
    )
    s.add(start_day[i] == start_day[i-1] + duration_prev - 1)

# Add event constraints
for i in range(6):
    # Hamburg must start on day 1
    s.add(Implies(order[i] == HAMBURG, start_day[i] == 1))
    # Dublin must start on day 2
    s.add(Implies(order[i] == DUBLIN, start_day[i] == 2))
    # Reykjavik must start on day 9
    s.add(Implies(order[i] == REYKJAVIK, start_day[i] == 9))

# Add end_day constraint for last city
last_city = order[5]
duration_last = If(last_city == HAMBURG, 2,
    If(last_city == DUBLIN, 5,
    If(last_city == REYKJAVIK, 2,
    If(last_city == LONDON, 5,
    If(last_city == HEL_SINKI, 4,
    If(last_city == MYKONOS, 3, 0 )))))
)
s.add(start_day[5] + duration_last - 1 == 16)

# Check for solution
if s.check() == sat:
    model = s.model()
    # Extract order and start_day values
    order_values = [model.evaluate(order[i]).as_long() for i in range(6)]
    start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(6)]
    
    # Get city names
    city_names = ['Hamburg', 'Dublin', 'Reykjavik', 'London', 'Helsinki', 'Mykonos']
    
    # Generate city_info: list of (city_name, start, end)
    city_info = []
    for i in range(6):
        city_idx = order_values[i]
        city_name = city_names[city_idx]
        start = start_day_values[i]
        dur = durations[city_idx]
        end = start + dur - 1
        city_info.append( (city_name, start, end) )
    
    # Generate day_to_city mapping
    day_to_city = {}
    for day in range(1, 17):
        for (city_name, start, end) in city_info:
            if start <= day <= end:
                day_to_city[day] = city_name
                break
    
    # Create itinerary list
    itinerary_list = [{'day': day, 'city': city} for day, city in day_to_city.items()]
    
    # Output JSON
    print(json.dumps({'itinerary': itinerary_list}, indent=2))
else:
    print("No solution found.")