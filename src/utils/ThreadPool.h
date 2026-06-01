/**
 * @file ThreadPool.h
 * @brief Thread pool implementation for parallel processing
 *
 * Provides a thread pool for executing tasks in parallel, improving
 * performance for file-intensive operations like diff processing.
 */

#ifndef ELOMIG_THREAD_POOL_H
#define ELOMIG_THREAD_POOL_H

#include <atomic>
#include <functional>
#include <future>
#include <mutex>
#include <queue>
#include <thread>
#include <vector>

#include <condition_variable>

namespace elomig {

/**
 * @brief Thread pool for parallel task execution
 *
 * Manages a pool of worker threads that execute queued tasks.
 * Tasks are enqueued via the enqueue() method and executed
 * in a thread-safe manner.
 */
class ThreadPool {
public:
	/**
	 * @brief Construct thread pool with specified number of threads
	 * @param threads Number of worker threads to create (default: hardware concurrency)
	 */
	explicit ThreadPool( size_t threads = std::thread::hardware_concurrency() );

	/**
	 * @brief Destroy thread pool
	 *
	 * Waits for all queued tasks to complete and shuts down all worker threads.
	 */
	~ThreadPool();

	// Delete copy constructor and assignment operator
	ThreadPool( ThreadPool const& )             = delete;
	ThreadPool& operator= ( ThreadPool const& ) = delete;

	/**
	 * @brief Enqueue a task for execution
	 *
	 * Adds a callable task to the execution queue. The task will be
	 * executed by one of the worker threads when available.
	 *
	 * @tparam F Type of callable function
	 * @param f Callable function to execute
	 * @return Future that will contain the result of the task
	 */
	template< class F >
	auto enqueue( F&& f ) -> std::future< typename std::result_of< F() >::type >;

	/**
	 * @brief Get number of worker threads
	 * @return Number of active worker threads
	 */
	size_t threadCount() const { return workers.size(); }

	/**
	 * @brief Check if pool is active
	 * @return True if pool is running
	 */
	bool isActive() const { return !stop.load(); }

private:
	std::vector< std::thread >            workers;     ///< Worker threads
	std::queue< std::function< void() > > tasks;       ///< Task queue
	std::mutex                            queue_mutex; ///< Mutex for task queue
	std::condition_variable               condition;   ///< Condition variable for task notification
	std::atomic< bool >                   stop;        ///< Stop flag for shutdown
};

} // namespace elomig

#include "ThreadPool.tcc" // Template implementation

#endif                    // ELOMIG_THREAD_POOL_H
