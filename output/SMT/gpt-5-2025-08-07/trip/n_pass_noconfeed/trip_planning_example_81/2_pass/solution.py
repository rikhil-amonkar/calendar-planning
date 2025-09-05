import json
from z3 import Solver, Int, Bool, Sum, If, And, Or, sat

def plan_trip():
    # Cities encoding
    MYKONOS, BUDAPEST, HAMBURG = 0, 1, 2
    city_names = {MYKONOS: "Mykonos", BUDAPEST: "Budapest", HAMBURG: "Hamburg"}
    cities = [MYKONOS, BUDAPEST, HAMBURG]

    # Trip parameters
    total_days = 9
    # Required presence days (counting flight days in both departure and arrival cities)
    required_days = {
        MYKONOS: 6,
        BUDAPEST: 3,
        HAMBURG: 2
    }
    # Conference requirements: must be in Mykonos on these days (can be via flight)
    conference_days_mykonos = [4, 9]

    # Allowed direct flights (undirected edges)
    allowed_edges = {
        (MYKONOS, BUDAPEST), (BUDAPEST, MYKONOS),
        (HAMBURG, BUDAPEST), (BUDAPEST, HAMBURG)
    }

    # Z3 Variables
    # loc[d] is the "base city" on day d (1..total_days), and loc[total_days+1] is the city at the end of last day (for possible flight on last day)
    loc = {d: Int(f"loc_{d}") for d in range(1, total_days + 2)}

    s = Solver()

    # Domain constraints
    for d in range(1, total_days + 2):
        s.add(Or(loc[d] == MYKONOS, loc[d] == BUDAPEST, loc[d] == HAMBURG))

    # Define flight indicator for each day (1..total_days)
    flight = {d: Bool(f"flight_{d}") for d in range(1, total_days + 1)}
    for d in range(1, total_days + 1):
        s.add(flight[d] == (loc[d] != loc[d + 1]))

        # Enforce only direct flights or staying in same city
        s.add(Or(
            loc[d] == loc[d + 1],
            Or(*[And(loc[d] == a, loc[d + 1] == b) for (a, b) in allowed_edges])
        ))

    # Total city-day counts considering flight days count for both departure and arrival cities
    for c in cities:
        count_c = Sum([
            If(loc[d] == c, 1, 0) + If(And(loc[d] != loc[d + 1], loc[d + 1] == c), 1, 0)
            for d in range(1, total_days + 1)
        ])
        s.add(count_c == required_days[c])

    # Number of flights equals excess city-days over total_days
    # sum(required_days.values()) = total_days + number_of_flights
    number_of_flights = sum(required_days.values()) - total_days
    s.add(Sum([If(flight[d], 1, 0) for d in range(1, total_days + 1)]) == number_of_flights)

    # Conference constraints: must be in Mykonos on specified days
    for day in conference_days_mykonos:
        presence = Or(
            loc[day] == MYKONOS,                               # base city that day
            And(loc[day] != loc[day + 1], loc[day + 1] == MYKONOS)  # arrival to Mykonos that day
        )
        s.add(presence)

    # Solve
    if s.check() != sat:
        return {"itinerary": []}

    m = s.model()
    loc_val = {d: m[loc[d]].as_long() for d in range(1, total_days + 2)}

    # Build itinerary segments with overlapping flight days
    change_days = [d for d in range(1, total_days + 1) if loc_val[d] != loc_val[d + 1]]

    segments = []
    if number_of_flights == 0:
        segments.append({"start": 1, "end": total_days, "city": loc_val[1]})
    else:
        starts = [1] + change_days
        ends = change_days + [total_days]
        for i in range(len(starts)):
            start_day = starts[i]
            end_day = ends[i]
            if i == 0:
                city_code = loc_val[1]
            else:
                d = starts[i]
                city_code = loc_val[d + 1]  # arrival city for the segment starting at change day d
            segments.append({"start": start_day, "end": end_day, "city": city_code})

    itinerary = []
    for seg in segments:
        itinerary.append({
            "day_range": f"Day {seg['start']}-{seg['end']}",
            "place": city_names[seg["city"]]
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_trip()
    print(json.dumps(result, ensure_ascii=False))