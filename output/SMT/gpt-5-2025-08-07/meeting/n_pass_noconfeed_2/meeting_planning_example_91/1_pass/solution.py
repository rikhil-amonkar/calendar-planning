import json
from z3 import Optimize, Int, Bool, If, And, Or, is_true, sat

def minutes_to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def compute_schedule():
    # Input parameters
    params = {
        "locations": ["Russian Hill", "Richmond District"],
        "travel_minutes": {
            ("Russian Hill", "Richmond District"): 14,
            ("Richmond District", "Russian Hill"): 13
        },
        "arrival_at_russian_hill": "9:00",
        "people": {
            "Daniel": {
                "location": "Richmond District",
                "availability_start": "19:00",
                "availability_end": "20:15",
                "min_meeting_minutes": 75
            }
        }
    }

    # Convert time strings to minutes from midnight
    def parse_time(tstr):
        h, m = map(int, tstr.split(":"))
        return h * 60 + m

    arrival_rh = parse_time(params["arrival_at_russian_hill"])
    daniel_start = parse_time(params["people"]["Daniel"]["availability_start"])
    daniel_end = parse_time(params["people"]["Daniel"]["availability_end"])
    min_meeting = params["people"]["Daniel"]["min_meeting_minutes"]
    travel_rh_to_rd = params["travel_minutes"][("Russian Hill", "Richmond District")]
    day_end = 24 * 60

    # Z3 model
    opt = Optimize()
    opt.set(priority='lex')

    # Decision variables
    meet_d = Bool("meet_daniel")

    depart_rh = Int("depart_russian_hill_to_richmond")
    arrive_rd = Int("arrive_richmond")
    meet_start = Int("meet_start_daniel")
    meet_end = Int("meet_end_daniel")

    # Bounds for all time variables (within the day)
    opt.add(depart_rh >= 0, depart_rh <= day_end)
    opt.add(arrive_rd >= 0, arrive_rd <= day_end)
    opt.add(meet_start >= 0, meet_start <= day_end)
    opt.add(meet_end >= 0, meet_end <= day_end)

    # Meeting and travel constraints when meeting Daniel
    meeting_constraints = And(
        # Start from Russian Hill at/after arrival time
        depart_rh >= arrival_rh,
        # Travel from Russian Hill to Richmond District
        arrive_rd == depart_rh + travel_rh_to_rd,
        # Arrive before or at meeting start
        meet_start >= arrive_rd,
        # Respect Daniel's availability window
        meet_start >= daniel_start,
        meet_end <= daniel_end,
        # Meeting duration at least the minimum
        meet_end - meet_start >= min_meeting,
        meet_start < meet_end
    )

    # Either we meet Daniel and satisfy constraints, or we don't meet and times collapse
    opt.add(If(meet_d, meeting_constraints, And(
        meet_start == 0,
        meet_end == 0
    )))

    # Optimization goals:
    # 1) Maximize the number of friends met (Daniel = 1 if met, else 0)
    meet_count = Int("meet_count")
    opt.add(meet_count == If(meet_d, 1, 0))
    h1 = opt.maximize(meet_count)

    # 2) Maximize total meeting duration (within feasible window)
    total_meeting_minutes = Int("total_meeting_minutes")
    opt.add(total_meeting_minutes == If(meet_d, meet_end - meet_start, 0))
    h2 = opt.maximize(total_meeting_minutes)

    # 3) Minimize waiting time upon arrival at meeting location
    waiting_at_rd = Int("waiting_at_richmond")
    opt.add(waiting_at_rd == If(meet_d, meet_start - arrive_rd, 0))
    h3 = opt.minimize(waiting_at_rd)

    # Solve
    if opt.check() != sat:
        # No feasible schedule
        result = {"itinerary": []}
        print(json.dumps(result))
        return

    model = opt.model()
    itinerary = []

    if is_true(model[meet_d]):
        s = model[meet_start].as_long()
        e = model[meet_end].as_long()
        itinerary.append({
            "action": "meet",
            "location": params["people"]["Daniel"]["location"],
            "person": "Daniel",
            "start_time": minutes_to_hhmm(s),
            "end_time": minutes_to_hhmm(e)
        })

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    compute_schedule()