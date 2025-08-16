from z3 import *

# We assign an integer to each city as follows:
# 0: Reykjavik (4 days)
# 1: Riga (2 days)
# 2: Oslo (3 days)
# 3: Lyon (5 days)
# 4: Dubrovnik (2 days)
# 5: Madrid (2 days)
# 6: Warsaw (4 days)
# 7: London (3 days)

# In our itinerary the overall calendar is 18 days.
# Because when flying between two cities on a given day that day counts for both cities,
# the sum of the “city‐stay days” is 25 = 18 + 7 (7 flight overlaps).
# Thus if a city at position i is visited starting on day S[i] with required duration d,
# its interval is [S[i], S[i]+d−1] and S[0] is 1 while for i=0..6, S[i+1] = S[i] + d(x[i]) − 1,
# and finally S[7] + d(x[7]) − 1 = 18.

# Some extra “absolute‐time” conditions:
# • When in Riga (city 1) you must meet a friend – the visit interval must cover day 4 or day 5.
# • When in Dubrovnik (city 4) you must attend a wedding – the visit interval must cover day 7 or day 8.

# Allowed direct flight connections (when flying on day X the itinerary is in both cities on day X):
# In almost all cases the flight can go either way except that “from Reykjavik to Madrid” is one–directional!
# The allowed ordered connected pairs (a,b) are:
#
#   (6,0) and (0,6)         [Warsaw – Reykjavik]
#   (2,5) and (5,2)         [Oslo – Madrid]
#   (6,1) and (1,6)         [Warsaw – Riga]
#   (3,7) and (7,3)         [Lyon – London]
#   (5,7) and (7,5)         [Madrid – London]
#   (6,7) and (7,6)         [Warsaw – London]
#   (0,5)                  [Reykjavik -> Madrid only]
#   (6,2) and (2,6)         [Warsaw – Oslo]
#   (2,4) and (4,2)         [Oslo – Dubrovnik]
#   (2,0) and (0,2)         [Oslo – Reykjavik]
#   (1,2) and (2,1)         [Riga – Oslo]
#   (2,3) and (3,2)         [Oslo – Lyon]
#   (2,7) and (7,2)         [Oslo – London]
#   (7,0) and (0,7)         [London – Reykjavik]
#   (6,5) and (5,6)         [Warsaw – Madrid]
#   (5,3) and (3,5)         [Madrid – Lyon]
#   (4,5) and (5,4)         [Dubrovnik – Madrid]

# We will use Z3 to choose the order of the 8 cities (a permutation) and automatically “schedule” the start day S[i] for each city.
# Then each consecutive pair will have to satisfy one of the allowed flight connections.
# We also add the meeting/wedding time‐window constraints on Riga and Dubrovnik.

# Define a function returning the required duration (in days) for a city
def duration(city):
    return If(city == 0, 4,
           If(city == 1, 2,
           If(city == 2, 3,
           If(city == 3, 5,
           If(city == 4, 2,
           If(city == 5, 2,
           If(city == 6, 4, 3)))))))

# Define allowed flight transitions between cities a and b.
def allowed(a, b):
    return Or(
        And(a == 6, b == 0), And(a == 0, b == 6),   # Warsaw <-> Reykjavik
        And(a == 2, b == 5), And(a == 5, b == 2),   # Oslo <-> Madrid
        And(a == 6, b == 1), And(a == 1, b == 6),   # Warsaw <-> Riga
        And(a == 3, b == 7), And(a == 7, b == 3),   # Lyon <-> London
        And(a == 5, b == 7), And(a == 7, b == 5),   # Madrid <-> London
        And(a == 6, b == 7), And(a == 7, b == 6),   # Warsaw <-> London
        And(a == 0, b == 5),                         # Reykjavik -> Madrid only
        And(a == 6, b == 2), And(a == 2, b == 6),   # Warsaw <-> Oslo
        And(a == 2, b == 4), And(a == 4, b == 2),   # Oslo <-> Dubrovnik
        And(a == 2, b == 0), And(a == 0, b == 2),   # Oslo <-> Reykjavik
        And(a == 1, b == 2), And(a == 2, b == 1),   # Riga <-> Oslo
        And(a == 2, b == 3), And(a == 3, b == 2),   # Oslo <-> Lyon
        And(a == 2, b == 7), And(a == 7, b == 2),   # Oslo <-> London
        And(a == 7, b == 0), And(a == 0, b == 7),   # London <-> Reykjavik
        And(a == 6, b == 5), And(a == 5, b == 6),   # Warsaw <-> Madrid
        And(a == 5, b == 3), And(a == 3, b == 5),   # Madrid <-> Lyon
        And(a == 4, b == 5), And(a == 5, b == 4)    # Dubrovnik <-> Madrid
    )

solver = Solver()

N = 8  # total number of cities
# x[i] will be the city assigned to the i-th leg (in the order you visit them)
x = [Int("x_%d" % i) for i in range(N)]
# S[i] will be the starting calendar day for the stay in the i-th visited city.
S = [Int("S_%d" % i) for i in range(N)]

# Each x[i] is in the domain 0..7 and they’re all different (each city is visited exactly once)
for i in range(N):
    solver.add(x[i] >= 0, x[i] <= 7)
solver.add(Distinct(x))

# The itinerary starts on day 1.
solver.add(S[0] == 1)

# For each visited city (except the last), the next city’s start day is:
# S[i+1] = S[i] + (duration of city at x[i]) - 1
for i in range(N-1):
    solver.add(S[i+1] == S[i] + duration(x[i]) - 1)

# The final city must end exactly on day 18:
solver.add(S[N-1] + duration(x[N-1]) - 1 == 18)

# For each consecutive pair of cities, the direct flight used must be allowed.
for i in range(N-1):
    solver.add(allowed(x[i], x[i+1]))

# Friend meeting in Riga: if a leg is in Riga (city 1), its interval [S, S + duration - 1] must contain day 4 or day 5.
for i in range(N):
    solver.add(Implies(x[i] == 1,
                       Or(And(S[i] <= 4, 4 <= S[i] + duration(x[i]) - 1),
                          And(S[i] <= 5, 5 <= S[i] + duration(x[i]) - 1))))

# Wedding in Dubrovnik: if a leg is in Dubrovnik (city 4), its interval must contain day 7 or day 8.
for i in range(N):
    solver.add(Implies(x[i] == 4,
                       Or(And(S[i] <= 7, 7 <= S[i] + duration(x[i]) - 1),
                          And(S[i] <= 8, 8 <= S[i] + duration(x[i]) - 1))))

if solver.check() == sat:
    m = solver.model()
    # Define the city names for output.
    city_names = {
        0: "Reykjavik",
        1: "Riga",
        2: "Oslo",
        3: "Lyon",
        4: "Dubrovnik",
        5: "Madrid",
        6: "Warsaw",
        7: "London"
    }
    # Build the itinerary: for each visited city, list the city name and its day interval.
    itinerary = []
    for i in range(N):
        city_index = m.evaluate(x[i]).as_long()
        start_day = m.evaluate(S[i]).as_long()
        # Compute duration based on the city (same as in the duration() function above)
        if city_index == 0:
            d = 4
        elif city_index == 1:
            d = 2
        elif city_index == 2:
            d = 3
        elif city_index == 3:
            d = 5
        elif city_index == 4:
            d = 2
        elif city_index == 5:
            d = 2
        elif city_index == 6:
            d = 4
        else:
            d = 3
        end_day = start_day + d - 1
        itinerary.append({"city": city_names[city_index], "start": start_day, "end": end_day})
    
    # Output the itinerary as a JSON-formatted dictionary.
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")