from z3 import Solver, Int, IntVector, Distinct, Sum, And, Or, If, sat

# -----------------------------------------------------------------------------
# We have 10 cities. We assign an index and specify:
#  City         Index   Planned Duration   Event (if any)
#  ------------------------------------------------------------
#  Paris         0      5 days             Friends meeting between day 4 and 8 
#  Warsaw        1      2 days             (no event; note: see discussion below)
#  Krakow        2      2 days             Workshop between day 17 and 18
#  Tallinn       3      2 days             (no event)
#  Riga          4      2 days             Wedding between day 23 and 24
#  Copenhagen    5      5 days             (no event)
#  Helsinki      6      5 days             Friend meeting between day 18 and 22
#  Oslo          7      5 days             (no event)
#  Santorini     8      2 days             Visit relatives between day 12 and 13
#  Lyon          9      4 days             (no event)
#
# IMPORTANT NOTE ON TOTAL TRIP LENGTH:
# In our earlier scheduling model, when visiting n cities, the effective trip
# length is (full duration for the 1st city) + (sum of (duration - 1) for later cities).
# With the above durations, that equals:
#     5 + (2-1)+(2-1)+(2-1)+(2-1)+(5-1)+(5-1)+(5-1)+(2-1)+(4-1)
#   = 5 + 1+1+1+1+4+4+4+1+3 = 5 + 20 = 25.
# (Because there are 9 flights and each flight “uses up” one day of a later visit.)
#
# To allow some flexibility, we also allow extra waiting days between cities.
# In our case, to obtain exactly 25 days total, the extra waiting (overhead) must sum to 0.
# However, if you wish to allow waiting days (for less rigidity) you could
# require Sum(w) == extra, where extra = total_trip - (sum(durations) - (n-1)).
# Here, sum(durations)=5+2+2+2+2+5+5+5+2+4 = 32, and (n-1)=9, so 32-9 = 23.
# To get 25 days total, we require extra waiting of 2 days.
# We'll use that model: Each flight (i.e. each transition between cities) may
# incur a nonnegative waiting time w[i], and we force Sum(w) == 2.
#
# SCHEDULE MODEL:
#   Let pos[i] be the city visited at itinerary position i (0 <= i <= 9).
#   Let S[i] be the arrival day (integer) at the city in position i.
#   The visit in a city always lasts exactly its planned duration.
#
#   For the 1st city, the visit interval is [S[0], S[0]+duration-1].
#   For any later city, due to the flight “loss”, we model its effective contribution as (duration - 1).
#   More precisely, we use the recurrence:
#       S[0] = 1.
#       S[1] = S[0] + duration(pos[0])         + w[0]
#       S[i] = S[i-1] + (duration(pos[i-1]) - 1)  + w[i-1]    for i>=2.
#
#   The departure day of the city in position i is:
#       if i == 0:  departure = S[0] + duration(pos[0]) - 1
#       else:       departure = S[i] + (duration(pos[i]) - 1)
#
#   The trip ends exactly at day 25:
#       S[9] + (duration(pos[9]) - 1) == 25.
#
#   Extra waiting: Let w[0]..w[8] be the waiting days added at each transition.
#       Each w[i] >= 0, and we require Sum(w) == 2.
#
# EVENT CONSTRAINTS:
#  - In Paris (index 0), you want to meet your friends between day 4 and 8.
#      The visit interval in Paris is [S, S+5-1] (whether first or later, it comes out the same since 5-1=4)
#      For the meeting to be possible, we require that the interval covers some day in [4,8].
#      A sufficient condition is: arrival S <= 8.
#
#  - In Krakow (index 2), you must attend a workshop between day 17 and 18.
#      The visit interval in Krakow is [S, S+2-1] = [S, S+1]. To cover [17,18] the interval must
#      include that window. This forces S to be at least 16 (so S+1 >=17) and at most 18 (so that S <= 18).
#
#  - In Riga (index 4), you will attend a wedding between day 23 and 24.
#      The visit interval is [S, S+2-1] = [S, S+1]. So require S >= 22 and S <= 24.
#
#  - In Helsinki (index 6), you want to meet a friend between day 18 and 22.
#      The visit interval is [S, S+5-1] = [S, S+4]. So require S >= 14 (S+4>=18) and S <= 22.
#
#  - In Santorini (index 8), you plan to visit relatives between day 12 and 13.
#      The visit interval is [S, S+2-1] = [S, S+1]. So require S >= 11 and S <= 13.
#
# Also, note that for some events it is impossible to satisfy the event if that city
# is visited first because the fixed start S[0] = 1 would not allow reaching a late event.
# Therefore, we force that if a city with a later event is chosen, it must not be the first city.
# In our case, Krakow (2), Riga (4), Helsinki (6) and Santorini (8) cannot be visited first.
#
# ALLOWED FLIGHTS:
# The problem specifies the following direct flights (each pair is bidirectional unless noted otherwise):
#
#  Warsaw <-> Riga                      (1,4) and (4,1)
#  Warsaw <-> Tallinn                   (1,3) and (3,1)
#  Copenhagen <-> Helsinki              (5,6) and (6,5)
#  Lyon <-> Paris                       (9,0) and (0,9)
#  Copenhagen <-> Warsaw                (5,1) and (1,5)
#  Lyon <-> Oslo                        (9,7) and (7,9)
#  Paris <-> Oslo                       (0,7) and (7,0)
#  Paris <-> Riga                       (0,4) and (4,0)
#  Krakow <-> Helsinki                  (2,6) and (6,2)
#  Paris <-> Tallinn                    (0,3) and (3,0)
#  Oslo <-> Riga                        (7,4) and (4,7)
#  Krakow <-> Warsaw                    (2,1) and (1,2)
#  Paris <-> Helsinki                   (0,6) and (6,0)
#  Copenhagen <-> Santorini             (5,8) and (8,5)
#  Helsinki <-> Warsaw                  (6,1) and (1,6)
#  Helsinki <-> Riga                    (6,4) and (4,6)
#  Copenhagen <-> Riga                  (5,4) and (4,5)
#  Paris <-> Krakow                     (0,2) and (2,0)
#  Copenhagen <-> Oslo                  (5,7) and (7,5)
#  Oslo <-> Tallinn                     (7,3) and (3,7)
#  Oslo <-> Helsinki                    (7,6) and (6,7)
#  Copenhagen <-> Tallinn               (5,3) and (3,5)
#  Oslo <-> Krakow                      (7,2) and (2,7)
#  Riga -> Tallinn                      (4,3) only (directed from Riga to Tallinn)
#  Helsinki <-> Tallinn                 (6,3) and (3,6)
#  Paris <-> Copenhagen                 (0,5) and (5,0)
#  Paris <-> Warsaw                     (0,1) and (1,0)
#  Santorini -> Oslo                    (8,7) only (directed from Santorini to Oslo)
#  Oslo <-> Warsaw                      (7,1) and (1,7)
#
# -----------------------------------------------------------------------------
# We now set up the Z3 model.
# -----------------------------------------------------------------------------

# City data
cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen",
          "Helsinki", "Oslo", "Santorini", "Lyon"]
durations = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]  # as given

n = 10
total_trip = 25

s = Solver()

# Decision variables:
# pos[i] : city at itinerary position i (0-indexed)
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# S[i] : arrival day at city in position i
S = IntVector("S", n)
s.add(S[0] == 1)
for i in range(n):
    s.add(S[i] >= 1)

# w[i] : extra waiting days after city at position i, for i = 0,..., n-2.
w = IntVector("w", n-1)
for i in range(n-1):
    s.add(w[i] >= 0)
# Total extra waiting must sum to 2.
s.add(Sum(w) == 2)

# Recurrence for arrival days:
# For position 1: S[1] = S[0] + (full duration of first city) + w[0].
# For position i >= 2: S[i] = S[i-1] + (duration(previous)-1) + w[i-1].
for i in range(1, n):
    # For i == 1, use full duration; for i >=2, subtract one day.
    if i == 1:
        s.add(S[i] == S[0] + 
              Sum([If(pos[0] == c, durations[c], 0) for c in range(n)]) + w[0])
    else:
        s.add(S[i] == S[i-1] + 
              Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]) + w[i-1])

# Final departure day constraint:
# The departure day from the last city is S[n-1] + (duration(last)-1)
s.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Flights allowed: For every consecutive pair, the flight from city pos[i] to pos[i+1] must be allowed.
# Define the set of allowed directed pairs.
allowed_flights = {
    (1,4), (4,1),
    (1,3), (3,1),
    (5,6), (6,5),
    (9,0), (0,9),
    (5,1), (1,5),
    (9,7), (7,9),
    (0,7), (7,0),
    (0,4), (4,0),
    (2,6), (6,2),
    (0,3), (3,0),
    (7,4), (4,7),
    (2,1), (1,2),
    (0,6), (6,0),
    (5,8), (8,5),
    (6,1), (1,6),
    (6,4), (4,6),
    (5,4), (4,5),
    (0,2), (2,0),
    (5,7), (7,5),
    (7,3), (3,7),
    (7,6), (6,7),
    (5,3), (3,5),
    (7,2), (2,7),
    (4,3),    # directed from Riga to Tallinn
    (6,3), (3,6),
    (0,5), (5,0),
    (0,1), (1,0),
    (8,7),    # directed from Santorini to Oslo
    (7,1), (1,7)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(flight_options))

# Event Constraints:
for i in range(n):
    # For the city in position i, get its planned duration value (d)
    isParis    = (pos[i] == 0)
    isWarsaw   = (pos[i] == 1)
    isKrakow   = (pos[i] == 2)
    isTallinn  = (pos[i] == 3)
    isRiga     = (pos[i] == 4)
    isCopen    = (pos[i] == 5)
    isHelsinki = (pos[i] == 6)
    isOslo     = (pos[i] == 7)
    isSantor   = (pos[i] == 8)
    isLyon     = (pos[i] == 9)
    
    # Compute the visit's departure day:
    # if i==0: dept = S[i] + duration - 1, else dept = S[i] + (duration - 1)
    # (In our model the formula is the same for every position; the recurrence already 
    #  accounted for the flight loss for later cities.)
    dept = S[i] + Sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])
    
    # For Paris: meet friends between day 4 and 8.
    # A sufficient condition: arrival must be no later than day 8.
    s.add(If(isParis, S[i] <= 8, True))
    
    # For Krakow: workshop between day 17 and 18.
    # Visit interval is [S, S+1]. To cover day 17-18, we require:
    #   S + 1 >= 17   -> S >= 16  and S <= 18 (so that the interval [S, S+1] can “cover” day 18)
    s.add(If(isKrakow, And(S[i] >= 16, S[i] <= 18), True))
    
    # For Riga: wedding between day 23 and 24.
    # Interval: [S, S+1] must cover this window. So S >= 22 and S <= 24.
    s.add(If(isRiga, And(S[i] >= 22, S[i] <= 24), True))
    
    # For Helsinki: friend meeting between day 18 and 22.
    # Interval: [S, S+4] must cover some day in [18,22]. S >= 14 and S <= 22.
    s.add(If(isHelsinki, And(S[i] >= 14, S[i] <= 22), True))
    
    # For Santorini: visit relatives between day 12 and 13.
    # Interval: [S, S+1] must cover that window: S >= 11 and S <= 13.
    s.add(If(isSantor, And(S[i] >= 11, S[i] <= 13), True))
    
    # Additional: Some event cities cannot be the first city because S[0] = 1 would make it impossible:
    # Krakow, Riga, Helsinki, Santorini cannot be visited first.
    if i == 0:
        s.add(And(pos[0] != 2, pos[0] != 4, pos[0] != 6, pos[0] != 8))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city_name = cities[city_index]
        if i == 0:
            departure = arrivals[i] + durations[city_index] - 1
        else:
            departure = arrivals[i] + durations[city_index] - 1
        print(f" Position {i+1}: {city_name:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    print("Trip ends on Day:", m.evaluate(S[n-1] + durations[itinerary[-1]] - 1))
else:
    print("No valid trip plan could be found.")