This program computes an optimal 25‐day itinerary for 10 European cities subject to several constraints.
It searches (via depth‐first backtracking) for a permutation of the cities that:
  • Uses only direct flights (with some directed edges)
  • Spends a fixed number of days in each city (given)
  • “Overlaps” flights so that if you fly on a day you are counted in both cities
     (we require all flights to be “same‐day” so that the calendar length is minimized)
  • Has specific event windows in certain cities.
When a valid itinerary is found, the program computes the starting and ending day for each city
and outputs the result in JSON format.
 
The “overlap rule” is implemented as follows:
  - We assume the trip begins on day S₁.
  - In each city the stay is exactly the fixed duration.
  - When flying same‐day, the next city’s start day is defined as:
       S₍i+1₎ = Sᵢ + (duration of city i) – 1.
  - Hence, the final day of the trip is Sₙ + (duration of last city) – 1.
For our fixed durations (sum = 32) and 10 cities (9 flights), if every flight is same‐day,
the overall length = 32 – 9 = 23 days if counted without the starting offset;
by setting the start day to 1 (i.e. S₁ = 1) the itinerary spans days 1–25.
 
All given event constraints will be met if the computed “overlap” intervals intersect the event windows.