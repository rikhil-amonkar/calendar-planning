import itertools
import json

def minutes_to_time(minutes_since_900):
    total_minutes = minutes_since_900
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def main():
    travel_times = {
        "Financial District": {"Russian Hill": 10, "Sunset District": 31, "North Beach": 7, "The Castro": 23, "Golden Gate Park": 23},
        "Russian Hill": {"Financial District": 11, "Sunset District": 23, "North Beach": 5, "The Castro": 21, "Golden Gate Park": 21},
        "Sunset District": {"Financial District": 30, "Russian Hill": 24, "North Beach": 29, "The Castro": 17, "Golden Gate Park": 11},
        "North Beach": {"Financial District": 8, "Russian Hill": 4, "Sunset District": 27, "The Castro": 22, "Golden Gate Park": 22},
        "The Castro": {"Financial District": 20, "Russian Hill": 18, "Sunset District": 17, "North Beach": 20, "Golden Gate Park": 11},
        "Golden Gate Park": {"Financial District": 26, "Russian Hill": 19, "Sunset District": 10, "North Beach": 24, "The Castro": 13}
    }
    
    meetings = {
        "Patricia": ("Sunset District", 15, 780, 60),
        "Ronald": ("Russian Hill", 285, 495, 105),
        "Emily": ("The Castro", 435, 570, 60),
        "Mary": ("Golden Gate Park", 360, 450, 60)
    }
    laura_meeting = ("Laura", "North Beach", 210, 225, 15)
    
    scenarios = []
    
    # Scenario 1: Schedule Patricia in the morning
    events_scenario1 = []
    current_location = "Financial District"
    current_time = 0
    patricia = meetings["Patricia"]
    loc, s, e, d = patricia
    travel_time = travel_times[current_location][loc]
    arrive = current_time + travel_time
    start_meet = max(arrive, s)
    end_meet = start_meet + d
    if end_meet <= e:
        morning_schedule1 = [("Patricia", loc, start_meet, end_meet)]
        events_scenario1.append({
            "action": "travel",
            "from": current_location,
            "to": loc,
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(arrive)
        })
        events_scenario1.append({
            "action": "meet",
            "location": loc,
            "person": "Patricia",
            "start_time": minutes_to_time(start_meet),
            "end_time": minutes_to_time(end_meet)
        })
        current_location_after = loc
        current_time_after = end_meet
        
        travel_time_to_NB = travel_times[loc]["North Beach"]
        arrive_NB = current_time_after + travel_time_to_NB
        if arrive_NB <= 210:
            events_scenario1.append({
                "action": "travel",
                "from": loc,
                "to": "North Beach",
                "start_time": minutes_to_time(current_time_after),
                "end_time": minutes_to_time(arrive_NB)
            })
            events_scenario1.append({
                "action": "meet",
                "location": "North Beach",
                "person": "Laura",
                "start_time": minutes_to_time(210),
                "end_time": minutes_to_time(225)
            })
            current_loc_afternoon = "North Beach"
            current_time_afternoon = 225
            
            available_afternoon = [name for name in meetings if name != "Patricia"]
            best_afternoon1 = None
            best_count1 = 0
            best_finish1 = float('inf')
            if available_afternoon:
                for r in range(len(available_afternoon), 0, -1):
                    found = False
                    for perm in itertools.permutations(available_afternoon, r):
                        schedule_perm = []
                        cur_loc = current_loc_afternoon
                        cur_time = current_time_afternoon
                        valid = True
                        for name in perm:
                            mloc, ms, me, md = meetings[name]
                            ttime = travel_times[cur_loc][mloc]
                            arrive_time = cur_time + ttime
                            start_time_meet = max(arrive_time, ms)
                            if start_time_meet + md > me:
                                valid = False
                                break
                            end_time_meet = start_time_meet + md
                            schedule_perm.append((name, mloc, start_time_meet, end_time_meet))
                            cur_loc = mloc
                            cur_time = end_time_meet
                        if valid:
                            if r > best_count1:
                                best_count1 = r
                                best_finish1 = cur_time
                                best_afternoon1 = schedule_perm
                                found = True
                            elif r == best_count1 and cur_time < best_finish1:
                                best_finish1 = cur_time
                                best_afternoon1 = schedule_perm
                                found = True
                    if found:
                        break
            if best_afternoon1 is not None:
                cur_loc = current_loc_afternoon
                cur_time = current_time_afternoon
                for meeting in best_afternoon1:
                    ttime = travel_times[cur_loc][meeting[1]]
                    travel_start = cur_time
                    travel_end = cur_time + ttime
                    events_scenario1.append({
                        "action": "travel",
                        "from": cur_loc,
                        "to": meeting[1],
                        "start_time": minutes_to_time(travel_start),
                        "end_time": minutes_to_time(travel_end)
                    })
                    events_scenario1.append({
                        "action": "meet",
                        "location": meeting[1],
                        "person": meeting[0],
                        "start_time": minutes_to_time(meeting[2]),
                        "end_time": minutes_to_time(meeting[3])
                    })
                    cur_loc = meeting[1]
                    cur_time = meeting[3]
                total_meetings = 1 + 1 + best_count1
                scenarios.append((total_meetings, cur_time, events_scenario1))
    
    # Scenario 2: Do not schedule Patricia in the morning
    events_scenario2 = []
    current_location = "Financial District"
    current_time = 0
    travel_time_NB = travel_times["Financial District"]["North Beach"]
    arrive_NB = current_time + travel_time_NB
    if arrive_NB <= 210:
        events_scenario2.append({
            "action": "travel",
            "from": current_location,
            "to": "North Beach",
            "start_time": minutes_to_time(current_time),
            "end_time": minutes_to_time(arrive_NB)
        })
        events_scenario2.append({
            "action": "meet",
            "location": "North Beach",
            "person": "Laura",
            "start_time": minutes_to_time(210),
            "end_time": minutes_to_time(225)
        })
        current_loc_afternoon = "North Beach"
        current_time_afternoon = 225
        
        available_afternoon = list(meetings.keys())
        best_afternoon2 = None
        best_count2 = 0
        best_finish2 = float('inf')
        if available_afternoon:
            for r in range(len(available_afternoon), 0, -1):
                found = False
                for perm in itertools.permutations(available_afternoon, r):
                    schedule_perm = []
                    cur_loc = current_loc_afternoon
                    cur_time = current_time_afternoon
                    valid = True
                    for name in perm:
                        mloc, ms, me, md = meetings[name]
                        ttime = travel_times[cur_loc][mloc]
                        arrive_time = cur_time + ttime
                        start_time_meet = max(arrive_time, ms)
                        if start_time_meet + md > me:
                            valid = False
                            break
                        end_time_meet = start_time_meet + md
                        schedule_perm.append((name, mloc, start_time_meet, end_time_meet))
                        cur_loc = mloc
                        cur_time = end_time_meet
                    if valid:
                        if r > best_count2:
                            best_count2 = r
                            best_finish2 = cur_time
                            best_afternoon2 = schedule_perm
                            found = True
                        elif r == best_count2 and cur_time < best_finish2:
                            best_finish2 = cur_time
                            best_afternoon2 = schedule_perm
                            found = True
                if found:
                    break
        
        if best_afternoon2 is not None:
            cur_loc = current_loc_afternoon
            cur_time = current_time_afternoon
            for meeting in best_afternoon2:
                ttime = travel_times[cur_loc][meeting[1]]
                travel_start = cur_time
                travel_end = cur_time + ttime
                events_scenario2.append({
                    "action": "travel",
                    "from": cur_loc,
                    "to": meeting[1],
                    "start_time": minutes_to_time(travel_start),
                    "end_time": minutes_to_time(travel_end)
                })
                events_scenario2.append({
                    "action": "meet",
                    "location": meeting[1],
                    "person": meeting[0],
                    "start_time": minutes_to_time(meeting[2]),
                    "end_time": minutes_to_time(meeting[3])
                })
                cur_loc = meeting[1]
                cur_time = meeting[3]
            total_meetings = 1 + best_count2
            scenarios.append((total_meetings, cur_time, events_scenario2))
    
    if not scenarios:
        result = {"itinerary": []}
    else:
        scenarios.sort(key=lambda x: (-x[0], x[1]))
        best_scenario = scenarios[0][2]
        result = {"itinerary": best_scenario}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()