from z3 import Int, Solver, sat
import json

def main():
    total_days = 12

    # Required days in each city (with flight overlaps counted in both)
    required_naples_days = 3
    required_milan_days = 7
    required_seville_days = 4  # Also covers the annual show from day 9 to 12

    # Define flight day variables:
    # t1: day when flying from Naples to Milan
    # t2: day when flying from Milan to Seville
    t1 = Int('t1')
    t2 = Int('t2')

    s = Solver()

    # Domain constraints: flight days within the travel period and ordered
    s.add(t1 >= 1, t1 <= total_days)
    s.add(t2 >= 1, t2 <= total_days)
    s.add(t1 < t2)

    # Itinerary segments:
    # Naples segment: Days 1 to t1 (flight day is included in Naples)
    # Milan segment: Days t1 to t2 (flight day t1 counts for Milan, as does t2)
    # Seville segment: Days t2 to total_days (flight day t2 counts for Seville)
    #
    # The durations computed by these segments are:
    # Naples duration = t1 (since days 1..t1 => count is t1)
    # Milan duration = t2 - t1 + 1
    # Seville duration = total_days - t2 + 1

    # Add constraints to meet the required durations:
    s.add(t1 == required_naples_days)
    s.add(t2 - t1 + 1 == required_milan_days)
    s.add(total_days - t2 + 1 == required_seville_days)

    # Since the annual show in Seville is from day 9 to day 12,
    # the Seville segment must include these days.
    # With t2 determined by the duration constraint, this implies t2 <= 9.
    s.add(t2 <= 9)

    if s.check() == sat:
        m = s.model()
        flight_day_Naples_Milan = m[t1].as_long()
        flight_day_Milan_Seville = m[t2].as_long()

        itinerary = []
        itinerary.append({
            "day_range": f"Day 1-{flight_day_Naples_Milan}",
            "place": "Naples"
        })
        itinerary.append({
            "day_range": f"Day {flight_day_Naples_Milan}-{flight_day_Milan_Seville}",
            "place": "Milan"
        })
        itinerary.append({
            "day_range": f"Day {flight_day_Milan_Seville}-12",
            "place": "Seville"
        })

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()