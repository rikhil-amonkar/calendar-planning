This program computes an optimal 28‐day itinerary through 10 European cities,
subject to flight connectivity and time‐window constraints. The trip lasts 28 days
because the sum of the planned durations (37 days) minus 9 overlapping flight days equals 28.
A flight on a given day means that day is counted for both the departure and arrival cities.
The cities (with planned durations and any required time windows) are:
  • Brussels: 4 days
  • Naples: 4 days, must include a day between Day 5 and Day 8 (relatives visit)
  • Santorini: 5 days
  • Athens: 4 days, must include a day between Day 8 and Day 11 (workshop)
  • Copenhagen: 5 days, must include a day between Day 11 and Day 15 (friend meeting)
  • Prague: 2 days
  • Munich: 5 days
  • Dubrovnik: 3 days
  • Geneva: 3 days
  • Mykonos: 2 days, and its block must cover Day 27 and Day 28 (conference)

Only direct flights are available between certain pairs (the flight graph is defined below).
Note that Mykonos is forced to be the final city so that its 2‐day block falls on Days 27–28.

The program uses a backtracking search to build an itinerary order (fixing Mykonos last)
that satisfies the following:
  – Flight connectivity between consecutive cities.
  – Time‐window constraints in the required cities.
  – The “overlap” rule: if flying from city A to B on a transition day X,
    then day X counts toward both A and B.
The final itinerary is output as a JSON dictionary with key "itinerary" that
lists the day ranges for each city.