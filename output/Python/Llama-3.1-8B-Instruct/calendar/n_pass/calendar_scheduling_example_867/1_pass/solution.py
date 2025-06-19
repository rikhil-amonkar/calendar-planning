from datetime import datetime, timedelta

def schedule_meeting(betty_schedule, scott_schedule, meeting_duration, preferences):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    for day in days:
        if day == "Monday" or day == "Tuesday" or day == "Thursday":
            start_time = 9
        else:
            start_time = 9.5

        end_time = 17
        while start_time < end_time:
            start_hour = int(start_time)
            start_minute = 0
            end_hour = int(start_time) + 1
            end_minute = 0

            # Check if start time is available for both
            start_time_available = True
            for time in betty_schedule[day]:
                if start_time >= time[0] and start_time < time[1]:
                    start_time_available = False
                    break
            for time in scott_schedule[day]:
                if start_time >= time[0] and start_time < time[1]:
                    start_time_available = False
                    break

            if start_time_available:
                # Check if end time is available for both
                end_time_available = True
                for time in betty_schedule[day]:
                    if end_time > time[0] and end_time <= time[1]:
                        end_time_available = False
                        break
                for time in scott_schedule[day]:
                    if end_time > time[0] and end_time <= time[1]:
                        end_time_available = False
                        break

                if end_time_available:
                    # Check if meeting duration fits in the time slot
                    if end_time - start_time >= meeting_duration:
                        # Check if meeting day preference is met
                        if day!= "Wednesday" or preferences["avoid_wednesday"]:
                            # Print the proposed meeting time
                            print(f"{day}, {datetime(1900, 1, 1, start_hour, start_minute).strftime('%H:%M')} - {datetime(1900, 1, 1, end_hour, end_minute).strftime('%H:%M')}")
                            return

            # Increment the start time by 30 minutes
            start_time += 0.5

def main():
    betty_schedule = {
        "Monday": [(10, 10.5), (13.5, 14), (15, 15.5), (16, 16.5)],
        "Tuesday": [(9, 9.5), (11.5, 12), (12.5, 13), (13.5, 14), (16.5, 17)],
        "Wednesday": [(9.5, 10.5), (13, 13.5), (14, 14.5)],
        "Thursday": [(9.5, 10), (11.5, 12), (14, 14.5), (15, 15.5), (16.5, 17)]
    }

    scott_schedule = {
        "Monday": [(9.5, 15), (15.5, 16), (16.5, 17)],
        "Tuesday": [(9, 9.5), (10, 11), (11.5, 12), (12.5, 13.5), (14, 15), (16, 16.5)],
        "Wednesday": [(9.5, 12.5), (13, 13.5), (14, 14.5), (15, 15.5), (16, 16.5)],
        "Thursday": [(9, 9.5), (10, 10.5), (11, 12), (12.5, 13), (15, 16), (16.5, 17)]
    }

    meeting_duration = 0.5
    preferences = {"avoid_wednesday": True}

    schedule_meeting(betty_schedule, scott_schedule, meeting_duration, preferences)

if __name__ == "__main__":
    main()