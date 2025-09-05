import json
from z3 import Optimize, Int, Sum, If, And, Implies

def minutes(h, m=0):
    return h * 60 + m

def fmt_time(t):
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Locations and travel times (in minutes)
    travel = {
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', "Fisherman's Wharf"): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', "Fisherman's Wharf"): 5,
        ('North Beach', 'Bayview'): 22,
        ("Fisherman's Wharf", 'Nob Hill'): 11,
        ("Fisherman's Wharf", 'North Beach'): 6,
        ("Fisherman's Wharf", 'Bayview'): 26,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', "Fisherman's Wharf"): 25,
    }

    # People data
    persons = {
        'Helen': {
            'location': 'North Beach',
            'avail_start': minutes(7, 0),
            'avail_end': minutes(16, 45),
            'min_duration': 120
        },
        'Kimberly': {
            'location': "Fisherman's Wharf",
            'avail_start': minutes(16, 30),
            'avail_end': minutes(21, 0),
            'min_duration': 45
        },
        'Patricia': {
            'location': 'Bayview',
            'avail_start': minutes(18, 0),
            'avail_end': minutes(21, 15),
            'min_duration': 120
        }
    }

    people = list(persons.keys())
    loc = {p: persons[p]['location'] for p in people}
    avail_start = {p: persons[p]['avail_start'] for p in people}
    avail_end = {p: persons[p]['avail_end'] for p in people}
    min_dur = {p: persons[p]['min_duration'] for p in people}

    start_time_at_start_loc = minutes(9, 0)
    start_location = 'Nob Hill'

    opt = Optimize()

    # Decision variables
    visit = {p: Int(f"visit_{p}") for p in people}  # 0/1
    start_t = {p: Int(f"start_{p}") for p in people}
    end_t = {p: Int(f"end_{p}") for p in people}

    # Edge variables: from 'Start' and between people
    nodes_from = ['Start'] + people
    edges = {}
    for a in nodes_from:
        for b in people:
            if a == b:
                continue
            edges[(a, b)] = Int(f"e_{a}_{b}".replace(" ", "").replace("'", ""))  # 0/1

    # Domains and base constraints
    for p in people:
        opt.add(visit[p] >= 0, visit[p] <= 1)
        opt.add(start_t[p] >= 0, start_t[p] <= 24 * 60)
        opt.add(end_t[p] >= 0, end_t[p] <= 24 * 60)
        opt.add(end_t[p] >= start_t[p])

        # If visited, enforce availability and minimum duration
        opt.add(Implies(visit[p] == 1,
                        And(start_t[p] >= avail_start[p],
                            end_t[p] <= avail_end[p],
                            end_t[p] - start_t[p] >= min_dur[p])))

        # If not visited, force times to 0 to avoid inflating objective
        opt.add(Implies(visit[p] == 0, And(start_t[p] == 0, end_t[p] == 0)))

    for (a, b), e in edges.items():
        opt.add(e >= 0, e <= 1)

    # Predecessor constraints: each visited person has exactly one predecessor
    for b in people:
        preds = [edges[(a, b)] for a in nodes_from if a != b]
        opt.add(Sum(preds) == visit[b])

    # Outgoing constraints
    # Start must point to the first visited node if any are visited
    out_start = Sum([edges[('Start', b)] for b in people])
    total_visits = Sum([visit[p] for p in people])
    opt.add(out_start == If(total_visits == 0, 0, 1))

    # From each person, at most one outgoing edge, only if they are visited
    for a in people:
        succs = [edges[(a, b)] for b in people if b != a]
        opt.add(Sum(succs) <= visit[a])

    # Travel-time and sequencing constraints
    for (a, b), e in edges.items():
        if a == 'Start':
            # From initial location/time
            t_travel = travel[(start_location, loc[b])]
            opt.add(Implies(e == 1, start_t[b] >= start_time_at_start_loc + t_travel))
        else:
            # From person a to person b
            t_travel = travel[(loc[a], loc[b])]
            opt.add(Implies(e == 1, start_t[b] >= end_t[a] + t_travel))

    # Objective: maximize number of friends met, then total meeting time
    total_meeting_minutes = Sum([end_t[p] - start_t[p] for p in people])
    score = total_visits * 100000 + total_meeting_minutes
    opt.maximize(score)

    if opt.check().r == 1:  # sat
        m = opt.model()

        # Build itinerary by following the path from 'Start'
        itinerary = []

        # If no meetings, output empty itinerary
        if m.eval(total_visits).as_long() == 0:
            pass
        else:
            # Find the first person after Start
            current = None
            for b in people:
                if (('Start', b) in edges) and m.eval(edges[('Start', b)]).as_long() == 1:
                    current = b
                    break

            visited_chain = set()
            while current is not None and current not in visited_chain:
                visited_chain.add(current)
                st = m.eval(start_t[current]).as_long()
                et = m.eval(end_t[current]).as_long()
                itinerary.append({
                    "action": "meet",
                    "location": loc[current],
                    "person": current,
                    "start_time": fmt_time(st),
                    "end_time": fmt_time(et)
                })

                next_person = None
                for b in people:
                    if b != current and m.eval(edges[(current, b)]).as_long() == 1:
                        next_person = b
                        break
                current = next_person

        print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))
    else:
        # Infeasible: print empty itinerary
        print(json.dumps({"itinerary": []}, ensure_ascii=False))

if __name__ == "__main__":
    main()