#!/usr/bin/env python3
"""
Conversation manager for discussing problems with LLMs.
Tracks conversation history and facilitates multi-turn discussions.
"""

import os
import json
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional
from openai import OpenAI
from dotenv import load_dotenv

from dataset_loader import NaturalPlanDataset, TaskType

load_dotenv()


class ConversationManager:
    """Manages conversations with LLMs about Natural Plan problems."""
    
    def __init__(self, model: str = "gpt-3.5-turbo", save_dir: str = "conversations"):
        """
        Initialize the conversation manager.
        
        Args:
            model: Model to use (OpenAI or Deepseek)
            save_dir: Directory to save conversation logs
        """
        # Initialize appropriate API client based on model
        if model.startswith("deepseek-"):
            # Use Deepseek API
            self.client = OpenAI(
                api_key=os.getenv("DEEPSEEK_API_KEY"),
                base_url="https://api.deepseek.com"
            )
            self.api_provider = "deepseek"
        else:
            # Use OpenAI API
            self.client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
            self.api_provider = "openai"
        
        self.model = model
        self.save_dir = Path(save_dir)
        self.save_dir.mkdir(exist_ok=True)
        
        self.dataset = NaturalPlanDataset()
        
        # Current conversation state
        self.current_problem = None
        self.conversation_history = []
        self.conversation_id = None
        self.metadata = {}
    
    def start_conversation(self, 
                          task_type: TaskType, 
                          problem_index: int, 
                          split: str = "train",
                          shot_type: str = "0shot",
                          system_message: Optional[str] = None) -> str:
        """
        Start a new conversation about a problem.
        
        Args:
            task_type: Type of task
            problem_index: Index of the problem
            split: Data split
            shot_type: "0shot" or "5shot"
            system_message: Optional custom system message
        
        Returns:
            The formatted problem text
        """
        # Load the problem
        self.current_problem = self.dataset.get_problem(task_type, problem_index, split)
        
        # Initialize conversation
        self.conversation_history = []
        self.conversation_id = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        # Store metadata
        self.metadata = {
            "conversation_id": self.conversation_id,
            "task_type": task_type,
            "problem_index": problem_index,
            "problem_id": self.current_problem.get("id"),
            "split": split,
            "shot_type": shot_type,
            "model": self.model,
            "started_at": datetime.now().isoformat()
        }
        
        # Get the problem text
        problem_text = self.dataset.format_problem(self.current_problem, shot_type)
        
        # Set system message - include the problem in the system context
        if system_message is None:
            system_message = f"""You are a helpful AI assistant discussing planning and scheduling problems.

The user is working on the following problem:

{problem_text}

Please help them reason through this problem, provide solutions, and discuss alternatives when asked."""
        
        self.conversation_history.append({
            "role": "system",
            "content": system_message
        })
        
        return problem_text
    
    def send_message(self, user_message: str, temperature: float = 0.7) -> str:
        """
        Send a message to the LLM and get a response.
        
        Args:
            user_message: The user's message
            temperature: Sampling temperature
        
        Returns:
            The LLM's response
        """
        if not self.current_problem:
            raise ValueError("No active conversation. Call start_conversation() first.")
        
        # Add user message to history
        self.conversation_history.append({
            "role": "user",
            "content": user_message
        })
        
        # Prepare API call parameters
        api_params = {
            "model": self.model,
            "messages": self.conversation_history
        }
        
        # Reasoning models (O1, O3, GPT-5, Deepseek-Reasoner) don't support temperature parameter
        reasoning_models = ["o1", "o3", "gpt-5", "deepseek-reasoner"]
        if not any(self.model.lower().startswith(prefix) for prefix in reasoning_models):
            api_params["temperature"] = temperature
        
        # Get LLM response
        response = self.client.chat.completions.create(**api_params)
        
        assistant_message = response.choices[0].message.content
        
        # Add assistant response to history
        self.conversation_history.append({
            "role": "assistant",
            "content": assistant_message
        })
        
        return assistant_message
    
    def get_conversation_history(self) -> List[Dict]:
        """Get the full conversation history."""
        return self.conversation_history.copy()
    
    def get_golden_solution(self) -> str:
        """Get the golden solution for the current problem."""
        if not self.current_problem:
            raise ValueError("No active conversation.")
        return self.dataset.get_golden_solution(self.current_problem)
    
    def save_conversation(self, filename: Optional[str] = None) -> Path:
        """
        Save the conversation to a JSON file.
        
        Args:
            filename: Optional custom filename
        
        Returns:
            Path to the saved file
        """
        if not self.current_problem:
            raise ValueError("No active conversation to save.")
        
        if filename is None:
            filename = f"conversation_{self.conversation_id}.json"
        
        filepath = self.save_dir / filename
        
        # Prepare data to save
        data = {
            "metadata": self.metadata,
            "problem": self.current_problem,
            "conversation": self.conversation_history,
            "golden_solution": self.get_golden_solution()
        }
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)
        
        return filepath
    
    def load_conversation(self, filepath: str):
        """
        Load a saved conversation.
        
        Args:
            filepath: Path to the conversation file
        """
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        self.metadata = data["metadata"]
        self.current_problem = data["problem"]
        self.conversation_history = data["conversation"]
        self.conversation_id = self.metadata["conversation_id"]
    
    def display_conversation(self):
        """Display the conversation in a readable format."""
        print("\n" + "="*70)
        print(f"Conversation ID: {self.conversation_id}")
        print(f"Problem: {self.metadata.get('problem_id', 'N/A')}")
        print("="*70 + "\n")
        
        for msg in self.conversation_history:
            role = msg["role"].upper()
            content = msg["content"]
            
            if role == "SYSTEM":
                print(f"[{role}]")
                print(content)
                print("-" * 70 + "\n")
            elif role == "USER":
                print(f"[{role}]")
                print(content)
                print()
            elif role == "ASSISTANT":
                print(f"[{role}]")
                print(content)
                print("-" * 70 + "\n")


def main():
    """Demo usage of the conversation manager."""
    manager = ConversationManager()
    
    print("=== Starting Conversation with LLM ===\n")
    
    # Start a conversation about a calendar problem
    problem_text = manager.start_conversation(
        task_type="calendar",
        problem_index=0,
        shot_type="0shot"
    )
    
    print("Problem loaded:")
    print(problem_text)
    print("\n" + "="*70 + "\n")
    
    # Send first message
    print("Sending initial message to LLM...\n")
    response1 = manager.send_message(
        "Can you solve this scheduling problem? Please think step by step."
    )
    print("[ASSISTANT]")
    print(response1)
    print("\n" + "="*70 + "\n")
    
    # Follow-up question
    print("Sending follow-up question...\n")
    response2 = manager.send_message(
        "Is there any other time slot that could work?"
    )
    print("[ASSISTANT]")
    print(response2)
    print("\n" + "="*70 + "\n")
    
    # Show golden solution
    print("Golden Solution:")
    print(manager.get_golden_solution())
    print("\n" + "="*70 + "\n")
    
    # Save conversation
    filepath = manager.save_conversation()
    print(f"Conversation saved to: {filepath}")


if __name__ == "__main__":
    main()

