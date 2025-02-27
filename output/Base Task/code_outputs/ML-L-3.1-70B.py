class MeetingScheduler:
    def __init__(self):
        self.work_hours = (9, 17)  # 9:00 to 17:00
        self.meeting_duration = 0.5  # 30 minutes

    def find_available_time(self, harold_schedule, patrick_schedule):
        """
        Find the best available time for a meeting between Harold and Patrick.

        Args:
            harold_schedule (list): Harold's schedule (empty list if wide open)
            patrick_schedule (list): Patrick's schedule (list of tuples)

        Returns:
            tuple: Best available time for the meeting (start, end)
        """
        available_time = []
        current_time = self.work_hours[0]

        # Iterate through Patrick's schedule to find available time slots
        for schedule in patrick_schedule:
            if schedule[0] > current_time:
                available_time.append((current_time, schedule[0]))
            current_time = schedule[1]

        # Add the last available time slot if it exists
        if current_time < self.work_hours[1]:
            available_time.append((current_time, self.work_hours[1]))

        # Find the best available time slot that can fit the meeting duration
        for time_slot in available_time:
            if time_slot[1] - time_slot[0] >= self.meeting_duration:
                return time_slot

        return None


# Define Patrick's schedule
patrick_schedule = [(9, 9.5), (10.5, 12), (12.5, 13.5), (14, 14.5), (15, 16.5)]

# Create a meeting scheduler
scheduler = MeetingScheduler()

# Find the best available time for the meeting
available_time = scheduler.find_available_time([], patrick_schedule)

if available_time:
    print(f"Best available time for the meeting: {available_time[0]}:00 to {available_time[1]}:00")
else:
    print("No available time found for the meeting.")
