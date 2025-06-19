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
    morning_schedule1 = []
    current_location = "Financial District"
    current_time = 0
    patricia = meetings["Patricia"]
    loc, s, e, d = patricia
    travel_time = travel_times[current_location][loc]
    arrive = current_time + travel_time
    start_meet = max(arrive, s)
    end_meet = start_meet + d
    if end_meet <= e:
        morning_schedule1.append(("Patricia", loc, start_meet, end_meet))
        travel_time_to_NB = travel_times[loc]["North Beach"]
        arrive_NB = end_meet + travel_time_to_NB
        if arrive_NB <= 210:
            available_afternoon = [name for name in meetings if name != "Patricia"]
            current_loc_afternoon = "North Beach"
            current_time_afternoon = 225
            best_afternoon1 = None
            best_count1 = 0
            best_finish1 = float('inf')
            for perm in itertools.permutations(available_afternoon):
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
                    count_perm = len(perm)
                    if count_perm > best_count1 or (count_perm == best_count1 and cur_time < best_finish1):
                        best_count1 = count_perm
                        best_finish1 = cur_time
                        best_afternoon1 = schedule_perm
            if best_afternoon1 is not None:
                total_meetings = 1 + len(morning_schedule1) + best_count1
                full_schedule = []
                for m in morning_schedule1:
                    name, loc, start, end = m
                    full_schedule.append({
                        "action": "meet",
                        "location": loc,
                        "person": name,
                        "start_time": minutes_to_time(start),
                        "end_time": minutes_to_time(end)
                    })
                full_schedule.append({
                    "action": "meet",
                    "location": laura_meeting[1],
                    "person": laura_meeting[0],
                    "start_time": minutes_to_time(laura_meeting[2]),
                    "end_time": minutes_to_time(laura_meeting[3])
                })
                for m in best_afternoon1:
                    name, loc, start, end = m
                    full_schedule.append({
                        "action": "meet",
                        "location": loc,
                        "person": name,
                        "start_time": minutes_to_time(start),
                        "end_time": minutes_to_time(end)
                    })
                scenarios.append((total_meetings, best_finish1, full_schedule))
    
    # Scenario 2: Do not schedule Patricia in the morning
    morning_schedule2 = []
    current_location = "Financial District"
    travel_time = travel_times["Financial District"]["North Beach"]
    arrive_NB = 0 + travel_time
    if arrive_NB <= 210:
        available_afternoon = list(meetings.keys())
        current_loc_afternoon = "North Beach"
        current_time_afternoon = 225
        best_afternoon2 = None
        best_count2 = 0
        best_finish2 = float('inf')
        for perm in itertools.permutations(available_afternoon):
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
                count_perm = len(perm)
                if count_perm > best_count2 or (count_perm == best_count2 and cur_time < best_finish2):
                    best_count2 = count_perm
                    best_finish2 = cur_time
                    best_afternoon2 = schedule_perm
        if best_afternoon2 is not None:
            total_meetings = 1 + len(morning_schedule2) + best_count2
            full_schedule = []
            full_schedule.append({
                "action": "meet",
                "location": laura_meeting[1],
                "person": laura_meeting[0],
                "start_time": minutes_to_time(laura_meeting[2]),
                "end_time": minutes_to_time(laura_meeting[3])
            })
            for m in best_afternoon2:
                name, loc, start, end = m
                full_schedule.append({
                    "action": "meet",
                    "location": loc,
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
            scenarios.append((total_meetings, best_finish2, full_schedule))
    
    if not scenarios:
        result = {"itinerary": []}
    else:
        scenarios.sort(key=lambda x: (-x[0], x[1]))
        best_scenario = scenarios[0][2]
        result = {"itinerary": best_scenario}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()