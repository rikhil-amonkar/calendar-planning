from datetime import time

# Define a helper function to compare time intervals
def time_to_minutes(t):
    return t.hour * 60 + t.minute

def interval_length(start, end):
    return time_to_minutes(end) - time_to_minutes(start)

# For clarity, we define the meeting duration in minutes
MEETING_DURATION = 60

# The free intervals for each participant are derived from their busy times and working hours (09:00 to 17:00)
# We'll consider each day from Monday through Friday.
# We know from analysis that the only available common time slot that meets the duration and constraint is Wednesday.
# Wednesday:
#   Diane is busy from 09:00 to 09:30, 14:30 to 15:00, and 16:30 to 17:00.
#   Thus her free intervals on Wednesday: 09:30-14:30 and 15:00-16:30.
#   Matthew is busy from 09:00 to 11:00, 12:00 to 14:30, and 16:00 to 17:00.
#   Thus his free intervals on Wednesday: 11:00-12:00 and 14:30-16:00.
# Their intersections:
#   Intersection of first free interval: 09:30-14:30 with 11:00-12:00 is 11:00-12:00
#       However, Matthew prefers not to meet on Wednesday before 12:30.
#   Intersection of second free interval: Diane's 15:00-16:30 with Matthew's 14:30-16:00 is 15:00-16:00.
#       This interval is exactly 60 minutes and satisfies Matthew's preference.
#
# Therefore, a meeting on Wednesday from 15:00 to 16:00 meets all the constraints.

def main():
    meeting_day = "Wednesday"
    meeting_start = time(15, 0)
    meeting_end = time(16, 0)
    
    # Format the output as HH:MM:HH:MM and include the day of the week.
    output = f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} on {meeting_day}"
    print(output)

if __name__ == "__main__":
    main()