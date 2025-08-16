from z3 import Solver, Int
import json

# In this problem we must schedule a 16‐day trip across three cities:
#   • Bucharest (7 days, and you must be there at least one day between day 1 and day 7 for a wedding)
#   • Lyon (7 days)
#   • Porto (4 days)
#
# You only take direct flights between:
#   • Bucharest and Lyon 
#   • Lyon and Porto 
#
# When flying from one city to another on a day X, that day “counts” for both cities.
#
# Since the sum of required city days is 7 + 7 + 4 = 18 days,
# and each flight day counts double, you must have two flight days so that:
#
#    18 - (# flight days) = 16  =>  18 - 2 = 16
#
# A natural approach is to let:
#
#   • t1 = the flight day on which you depart Bucharest (i.e. you are in Bucharest days 1..t1 and 
#         t1 also counts as arrival day for Lyon).  Then Bucharest total days = t1.
#
#   • t2 = the flight day on which you depart Lyon (i.e. you are in Lyon from t1 through t2,
#         with both t1 and t2 counting in Lyon).  Then Lyon total days = t2 - t1 + 1.
#
#   • Finally, you are in Porto from t2 through day 16 (with t2 counting toward Porto).
#         Porto total days = 16 - t2 + 1.
#
# The constraints become:
#    Bucharest:     t1 == 7.
#    Lyon:          t2 - t1 + 1 == 7.
#    Porto:         16 - t2 + 1 == 4.
#
# Solving:
#    With t1 = 7, Lyon constraint gives t2 - 7 + 1 = 7  =>  t2 = 13.
#    Porto constraint becomes 16 - 13 + 1 = 4, which is correct.
#
# Additionally, the wedding in Bucharest must be scheduled between day 1 and day 7.
# Since the Bucharest interval is days 1..7 (counting the flight day t1 as well), that condition is satisfied.
#
# We then build an itinerary for days 1 to 16.
# On the flight days the traveler is in both cities:
#   • Day 7: Flight from Bucharest to Lyon → count Bucharest and Lyon.
#   • Day 13: Flight from Lyon to Porto → count Lyon and Porto.
#
# The following Python program uses the Z3 solver to “find” this solution and then creates an itinerary.
# In the output JSON the itinerary is a list of day mappings.
# On non-flight days the "place" value is a single string,
# while on flight days it is a list of two cities.
#
# Note: The itinerary below is consistent with the given example where a flight day
# counts for the city being departed from and the city being arrived to.
#
def main():
    s = Solver()
    
    # t1: flight day from Bucharest to Lyon
    # t2: flight day from Lyon to Porto
    t1 = Int('t1')
    t2 = Int('t2')
    
    # Basic bounds and ordering
    s.add(t1 >= 1, t1 <= 16, t2 >= 1, t2 <= 16, t1 < t2)
    
    # Constraint: It must be 7 days in Bucharest.
    # Since Bucharest is from day 1 to t1 (inclusive),
    # its total days equals t1. Set: t1 == 7.
    s.add(t1 == 7)
    
    # Constraint: 7 days in Lyon, where Lyon is scheduled from day t1 to t2 (inclusive).
    # This gives: (t2 - t1 + 1) == 7.
    s.add(t2 - t1 + 1 == 7)
    
    # Constraint: 4 days in Porto.
    # Porto is scheduled from day t2 to day 16 (inclusive),
    # so: (16 - t2 + 1) == 4.
    s.add(16 - t2 + 1 == 4)
    
    # The wedding in Bucharest must happen between day 1 and day 7.
    # Since the Bucharest period is days 1 to 7, the wedding condition is met.
    
    if s.check().r == 1:  # sat
        m = s.model()
        flight_day1 = m[t1].as_long()  # Should be 7
        flight_day2 = m[t2].as_long()  # Should be 13
        
        itinerary = []
        # Build a day-by-day itinerary. On flight days, include both cities.
        for day in range(1, 17):
            if day < flight_day1:
                # Before the first flight, the traveler is only in Bucharest.
                itinerary.append({"day": day, "place": "Bucharest"})
            elif day == flight_day1:
                # Flight day from Bucharest to Lyon. Counts for both.
                itinerary.append({"day": day, "place": ["Bucharest", "Lyon"]})
            elif flight_day1 < day < flight_day2:
                # In Lyon between the flights.
                itinerary.append({"day": day, "place": "Lyon"})
            elif day == flight_day2:
                # Flight day from Lyon to Porto. Counts for both.
                itinerary.append({"day": day, "place": ["Lyon", "Porto"]})
            else:
                # After the flight, the traveler is only in Porto.
                itinerary.append({"day": day, "place": "Porto"})
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("No valid solution found.")

if __name__ == '__main__':
    main()