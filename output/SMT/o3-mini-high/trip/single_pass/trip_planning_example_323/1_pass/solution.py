from z3 import Int, Solver
import json

# We will model the itinerary as 4 segments with 3 flight‐transitions.
# Let:
#   d2 = flight day when leaving London for Split.
#   d3 = flight day when leaving Split for Oslo.
#   d4 = flight day when leaving Oslo for Porto.
# We fix:
#   - London segment: from Day 1 to day d2. (Day d2 counts for both London and Split.)
#   - Split segment: from day d2 to day d3. (Day d2 counts for Split on arrival; day d3 counts for both Split and Oslo.)
#   - Oslo segment: from day d3 to day d4. (Day d3 counts for Oslo on arrival; day d4 counts for both Oslo and Porto.)
#   - Porto segment: from day d4 to day 16. (Day d4 counts for Porto on arrival.)
#
# The given requirements are:
#  - London: 7 days total (and visit relatives there between Day 1 and Day 7).
#  - Split: 5 days total and the annual show runs from Day 7 to Day 11.
#  - Oslo: 2 days total.
#  - Porto: 5 days total.
#
# Counting each segment with flight days counted twice:
#   London_count = d2 (since days 1 through d2 are in London, with d2 being the flight day).
#   Split_count  = (d3 - d2 + 1)  (arrival day d2 and departure day d3 count for Split).
#   Oslo_count   = (d4 - d3 + 1)  (arrival day d3 and departure day d4 count for Oslo).
#   Porto_count  = (16 - d4 + 1)  (arrival day d4 and then pure days thereafter).
#
# So we impose:
#   d2            = 7        (London gets 7 days and relatives are visited early).
#   (d3 - d2 + 1)= 5  => d3 = d2 + 4 = 11 (so Split covers days 7-11, as required for the show)
#   (d4 - d3 + 1)= 2  => d4 = d3 + 1 = 12 (Oslo covers 2 days)
#   (16 - d4 + 1)= 5  => d4 = 12 (Porto covers 5 days)
#
# The allowed flight connections (assumed bidirectional) are:
#   London <-> Split, 
#   London <-> Oslo,
#   Split <-> Oslo, 
#   Oslo <-> Porto.
#
# Our chosen transitions are:
#   Day d2 (7): London -> Split  (valid: London and Split have a direct flight)
#   Day d3 (11): Split -> Oslo   (valid: Split and Oslo have a direct flight)
#   Day d4 (12): Oslo -> Porto    (valid: Oslo and Porto have a direct flight)

# Define integer variables for flight days.
d2 = Int('d2')  # London to Split flight day
d3 = Int('d3')  # Split to Oslo flight day
d4 = Int('d4')  # Oslo to Porto flight day

s = Solver()

# All flight days must be within the trip (1 to 16) and in order.
s.add(d2 >= 1, d2 <= 16, d3 >= 1, d3 <= 16, d4 >= 1, d4 <= 16)
s.add(d2 < d3, d3 < d4)

# Impose the duration constraints:
s.add(d2 == 7)                # London: days 1 .. d2 => 7 days when d2 = 7.
s.add(d3 - d2 + 1 == 5)         # Split: days d2 .. d3 => 5 days, so d3 must be 11.
s.add(d4 - d3 + 1 == 2)         # Oslo: days d3 .. d4 => 2 days, so d4 must be 12.
s.add(16 - d4 + 1 == 5)         # Porto: days d4 .. 16 => 5 days.

if s.check() == 'sat':
    m = s.model()
    flight_day_london_split = m[d2].as_long()  # expected 7
    flight_day_split_oslo   = m[d3].as_long()  # expected 11
    flight_day_oslo_porto   = m[d4].as_long()  # expected 12

    itinerary = []
    # Build the itinerary for each day 1 to 16.
    for day in range(1, 17):
        # If day equals a flight day, assign both departure and arrival cities.
        if day == flight_day_london_split:
            # Flight from London to Split on this day.
            places = ["London", "Split"]
        elif day == flight_day_split_oslo:
            # Flight from Split to Oslo on this day.
            places = ["Split", "Oslo"]
        elif day == flight_day_oslo_porto:
            # Flight from Oslo to Porto on this day.
            places = ["Oslo", "Porto"]
        elif day < flight_day_london_split:
            # Before day 7, in London.
            places = ["London"]
        elif flight_day_london_split < day < flight_day_split_oslo:
            # After leaving London and before leaving Split: in Split.
            places = ["Split"]
        elif flight_day_split_oslo < day < flight_day_oslo_porto:
            # After arriving in Oslo (after leaving Split) and before leaving Oslo: in Oslo.
            places = ["Oslo"]
        else:  # day > flight_day_oslo_porto
            # After flight from Oslo, in Porto.
            places = ["Porto"]

        itinerary.append({"day": day, "places": places})

    # Prepare the final output dictionary.
    output = {"itinerary": itinerary}
    # Print JSON-formatted itinerary.
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")