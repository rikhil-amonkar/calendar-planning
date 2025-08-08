from z3 import *

# Define the variables for each day: 12 days
days = [Int('d_%d' % i) for i in range(1, 13)]

s = Solver()

# City encoding: 0 = Milan, 1 = Seville, 2 = Naples
s.add([Or(d == 0, d == 1, d == 2) for d in days])

# Constraint: From day 9 to 12, in Seville (which are indices 8 to 11 in zero-indexed list)
for i in [8, 9, 10, 11]:
    s.add(days[i] == 1)  # Seville is 1

# Direct flights: between Milan (0) and Seville (1), and between Milan (0) and Naples (2)
# So allowed transitions: (0,1), (1,0), (0,2), (2,0)
for i in range(0, 11):  # from day1 to day2, up to day11 to day12: 11 transitions
    current = days[i]
    next_day = days[i+1]
    s.add(If(current != next_day,
             Or(
                 And(current == 0, next_day == 1),
                 And(current == 1, next_day == 0),
                 And(current == 0, next_day == 2),
                 And(current == 2, next_day == 0)
             ),
             True))  # if no change, no constraint

# Function to count days for a city
def count_days_for_city(city_code, days_list):
    # First term: days where the city is assigned
    term1 = Sum([If(d == city_code, 1, 0) for d in days_list])
    # Second term: days i (from 0 to 10) where days_list[i] != city_code and days_list[i+1] == city_code
    term2 = Sum([If(And(days_list[i] != city_code, days_list[i+1] == city_code), 1, 0) for i in range(0, 11)])
    return term1 + term2

count_naples = count_days_for_city(2, days)
count_seville = count_days_for_city(1, days)
count_milan = count_days_for_city(0, days)

s.add(count_naples == 3)
s.add(count_seville == 4)
s.add(count_milan == 7)

# Solve the problem
if s.check() == sat:
    model = s.model()
    solution = [model[d].as_long() for d in days]
    # Convert to city names
    city_names = {0: "Milan", 1: "Seville", 2: "Naples"}
    itinerary_list = [{"day": i+1, "place": city_names[solution[i]]} for i in range(0, 12)]
    result = {'itinerary': itinerary_list}
    print(result)
else:
    print("No solution found")