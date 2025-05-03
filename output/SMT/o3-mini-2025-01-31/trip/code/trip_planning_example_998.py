from z3 import *

# City indices and durations:
# 0: Geneva    (5 days) – During day 11 to 15 you attend a conference in Geneva, so force arrival = 11.
# 1: Frankfurt (2 days)
# 2: Reykjavik (5 days)
# 3: Oslo      (4 days) – Meet your friends at Oslo between day 5 and 8, so force arrival = 5.
# 4: Vilnius   (2 days)
# 5: Tallinn   (3 days)
# 6: Dubrovnik (4 days)
#
# Total raw days = 5 + 2 + 5 + 4 + 2 + 3 + 4 = 25.
# With 6 overlaps (between consecutive visits) the overall trip length is 25 - 6 = 19 days.

cities = ["Geneva", "Frankfurt", "Reykjavik", "Oslo", "Vilnius", "Tallinn", "Dubrovnik"]
durations = [5, 2, 5, 4, 2, 3, 4]

# Allowed direct flights. Note that some flights are one-way.
# 1. Oslo and Frankfurt             -> (Oslo, Frankfurt) and (Frankfurt, Oslo) : (3,1), (1,3)
# 2. from Tallinn to Vilnius         -> one-way from Tallinn to Vilnius : (5,4)
# 3. Reykjavik and Oslo             -> (Reykjavik, Oslo) and (Oslo, Reykjavik) : (2,3), (3,2)
# 4. Dubrovnik and Frankfurt         -> (Dubrovnik, Frankfurt) and (Frankfurt, Dubrovnik) : (6,1), (1,6)
# 5. Oslo and Vilnius               -> (Oslo, Vilnius) and (Vilnius, Oslo) : (3,4), (4,3)
# 6. Oslo and Tallinn               -> (Oslo, Tallinn) and (Tallinn, Oslo) : (3,5), (5,3)
# 7. Frankfurt and Vilnius          -> (Frankfurt, Vilnius) and (Vilnius, Frankfurt) : (1,4), (4,1)
# 8. Geneva and Frankfurt           -> (Geneva, Frankfurt) and (Frankfurt, Geneva) : (0,1), (1,0)
# 9. Frankfurt and Tallinn          -> (Frankfurt, Tallinn) and (Tallinn, Frankfurt) : (1,5), (5,1)
# 10. Oslo and Dubrovnik            -> (Oslo, Dubrovnik) and (Dubrovnik, Oslo) : (3,6), (6,3)
# 11. Reykjavik and Frankfurt       -> (Reykjavik, Frankfurt) and (Frankfurt, Reykjavik) : (2,1), (1,2)
# 12. Dubrovnik and Geneva          -> (Dubrovnik, Geneva) and (Geneva, Dubrovnik) : (6,0), (0,6)
# 13. Oslo and Geneva               -> (Oslo, Geneva) and (Geneva, Oslo) : (3,0), (0,3)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a,b))
    allowed_flights.append((b,a))

# 1. Oslo <-> Frankfurt
add_bidirectional(3, 1)
# 2. from Tallinn -> Vilnius (one-way only)
allowed_flights.append((5, 4))
# 3. Reykjavik <-> Oslo
add_bidirectional(2, 3)
# 4. Dubrovnik <-> Frankfurt
add_bidirectional(6, 1)
# 5. Oslo <-> Vilnius
add_bidirectional(3, 4)
# 6. Oslo <-> Tallinn
add_bidirectional(3, 5)
# 7. Frankfurt <-> Vilnius
add_bidirectional(1, 4)
# 8. Geneva <-> Frankfurt
add_bidirectional(0, 1)
# 9. Frankfurt <-> Tallinn
add_bidirectional(1, 5)
# 10. Oslo <-> Dubrovnik
add_bidirectional(3, 6)
# 11. Reykjavik <-> Frankfurt
add_bidirectional(2, 1)
# 12. Dubrovnik <-> Geneva
add_bidirectional(6, 0)
# 13. Oslo <-> Geneva
add_bidirectional(3, 0)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Model the itinerary as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define the arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot, if city c is assigned then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival of the next equals the departure of the previous.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 19.
s.add(departures[n-1] == 19)

# Event-specific constraints:
# Geneva (index 0): Conference from day 11 to 15, so force arrival = 11.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 11, True))
# Oslo (index 3): Meet friends between day 5 and 8, so force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 5, True))

# Connectivity constraints:
# For each consecutive pair of cities in the itinerary, there must be an allowed direct flight.
for i in range(n-1):
    s.add(Or([And(order[i] == frm, order[i+1] == to)
              for (frm, to) in allowed_flights]))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")