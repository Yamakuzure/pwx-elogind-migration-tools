/**
 * @file ThreadPool.tcc
 * @brief Thread pool template implementation
 */

#include "ThreadPool.h"
#include "Logger.h"
#include <stdexcept>

namespace elomig {

inline ThreadPool::ThreadPool(size_t threads) : stop(false) {
    try {
        for (size_t i = 0; i < threads; ++i) {
            workers.emplace_back([this] {
                for (;;) {
                    std::function<void()> task;
                    
                    {
                        std::unique_lock<std::mutex> lock(this->queue_mutex);
                        this->condition.wait(lock, [this] { return this->stop.load() || !this->tasks.empty(); });
                        
                        if (this->stop.load() && this->tasks.empty()) {
                            break;
                        }
                        
                        task = std::move(this->tasks.front());
                        this->tasks.pop();
                    }
                    
                    task();
                }
            });
        }
        
        LOG_DEBUG("ThreadPool created with %zu threads", threads);
    } catch (const std::exception& e) {
        LOG_ERROR("Failed to create ThreadPool: %s", e.what());
        stop.store(true);
        throw;
    }
}

inline ThreadPool::~ThreadPool() {
    stop.store(true);
    condition.notify_all();
    
    for (std::thread& worker : workers) {
        if (worker.joinable()) {
            worker.join();
        }
    }
    
    LOG_DEBUG("ThreadPool destroyed");
}

template<class F>
inline auto ThreadPool::enqueue(F&& f) -> std::future<typename std::result_of<F()>::type> {
    using return_type = typename std::result_of<F()>::type;
    
    auto task = std::make_shared<std::packaged_task<return_type()>>(
        std::forward<F>(f)
    );
    
    std::future<return_type> res = task->get_future();
    
    {
        std::unique_lock<std::mutex> lock(queue_mutex);
        
        if (stop.load()) {
            throw std::runtime_error("enqueue on stopped ThreadPool");
        }
        
        tasks.emplace([task]() { (*task)(); });
    }
    
    condition.notify_one();
    return res;
}

} // namespace elomig